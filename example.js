// Just for viewing graphviz output
var fs = require('fs');

var Pipeline = require('json-pipeline');
var Reducer = require('json-pipeline-reducer');
var Scheduler = require('json-pipeline-scheduler');

//
// Create empty graph with CFG convenience
// methods.
//
var p = Pipeline.create('cfg');

//
// Parse the printable data and generate
// the graph.
//
p.parse(`pipeline {
  b0 {
    i0 = literal 0
    i1 = literal 0

    i3 = array
    i4 = jump ^b0
  }
  b0 -> b1

  b1 {
    i5 = ssa:phi ^b1 i0, i12
    i6 = ssa:phi ^i5, i1, i14

    i7 = loadArrayLength i3
    i8 = cmp "<", i6, i7
    i9 = if ^i6, i8
  }
  b1 -> b2, b3
  b2 {
    i10 = checkIndex ^b2, i3, i6
    i11 = load ^i10, i3, i6
    i12 = add i5, i11
    i13 = literal 1
    i14 = add i6, i13
    i15 = jump ^b2
  }
  b2 -> b1

  b3 {
    i16 = exit ^b3
  }
}`, { cfg: true }, 'printable');

if (process.env.DEBUG)
  fs.writeFileSync('before.gv', p.render('graphviz'));

//
// Just a helper to run reductions
//

function reduce(graph, reduction) {
  var reducer = new Reducer();
  reducer.addReduction(reduction);
  reducer.reduce(graph);

}

//
// Create reduction
//
var ranges = new Map();

function getRange(node) {
  if (ranges.has(node))
    return ranges.get(node);

  var range = { from: -Infinity, to: +Infinity, type: 'any' };
  ranges.set(node, range);
  return range;
}

function updateRange(node, reducer, from, to) {
  var range = getRange(node);

  // Lowest type, can't get upwards
  if (range.type === 'none')
    return;

  if (range.from === from && range.to === to && range.type === 'int')
    return;

  range.from = from;
  range.to = to;
  range.type = 'int';
  reducer.change(node);
}

function updateType(node, reducer, type) {
  var range = getRange(node);

  if (range.type === type)
    return;

  range.type = type;
  reducer.change(node);
}

//
// Set type of literal
//
function reduceLiteral(node, reducer) {
  var value = node.literals[0];
  updateRange(node, reducer, value, value);
}

function reduceBinary(node, left, right, reducer) {
  if (left.type === 'none' || right.type === 'none') {
    updateType(node, reducer, 'none');
    return false;
  }

  if (left.type === 'int' || right.type === 'int')
    updateType(node, reducer, 'int');

  if (left.type !== 'int' || right.type !== 'int')
    return false;

  return true;
}

//
// Just join the ranges of inputs
//
function reducePhi(node, reducer) {
  var left = getRange(node.inputs[0]);
  var right = getRange(node.inputs[1]);

  if (!reduceBinary(node, left, right, reducer))
    return;

  if (node.inputs[1].opcode !== 'add' || left.from !== left.to)
    return;

  var from = Math.min(left.from, right.from);
  var to = Math.max(left.to, right.to);
  updateRange(node, reducer, from, to);
}

//
// Detect: phi = phi + <positive number>, where initial phi is number,
// report proper range.
//
function reduceAdd(node, reducer) {
  var left = getRange(node.inputs[0]);
  var right = getRange(node.inputs[1]);

  if (!reduceBinary(node, left, right, reducer))
    return;

  var phi = node.inputs[0];
  if (phi.opcode !== 'ssa:phi' || right.from !== right.to)
    return;

  var number = right.from;
  if (number <= 0 || phi.inputs[1] !== node)
    return;

  var initial = getRange(phi.inputs[0]);
  if (initial.type !== 'int')
    return;

  updateRange(node, reducer, initial.from, +Infinity);
}

var limits = new Map();

function getLimit(node) {
  if (limits.has(node))
    return limits.get(node);

  var map = new Map();
  limits.set(node, map);
  return map;
}

function updateLimit(holder, node, reducer, type, value) {
  var map = getLimit(holder);
  if (!map.has(node))
    map.set(node, { type: 'any', value: null });

  var limit = map.get(node);
  if (limit.type === type && limit.value === value)
    return;
  limit.type = type;
  limit.value = value;
  reducer.change(holder);
}

function mergeLimit(node, reducer, other) {
  var map = getLimit(node);
  var otherMap = getLimit(other);

  otherMap.forEach(function(limit, key) {
    updateLimit(node, key, reducer, limit.type, limit.value);
  });
}

//
// Propagate limit from: X < Y to `if`'s true branch
//
function reduceIf(node, reducer) {
  var test = node.inputs[0];
  if (test.opcode !== 'cmp' || test.literals[0] !== '<')
    return;

  var left = test.inputs[0];
  var right = test.inputs[1];

  updateLimit(node.controlUses[0], left, reducer, '<', right);
  updateLimit(node.controlUses[2], left, reducer, '>=', right);
}

//
// Determine ranges and limits of
// the values.
//

var rangeAndLimit = new Reducer.Reduction({
  reduce: function(node, reducer) {
    if (node.opcode === 'literal')
      reduceLiteral(node, reducer);
    else if (node.opcode === 'ssa:phi')
      reducePhi(node, reducer);
    else if (node.opcode === 'add')
      reduceAdd(node, reducer);
    else if (node.opcode === 'if')
      reduceIf(node, reducer);
  }
});
reduce(p, rangeAndLimit);

//
// Now that we have ranges and limits,
// time to remove the useless array
// length checks.
//

function reduceCheckIndex(node, reducer) {
  // Walk up the control chain
  var region = node.control[0];
  while (region.opcode !== 'region' && region.opcode !== 'start')
    region = region.control[0];

  var array = node.inputs[0];
  var index = node.inputs[1];

  var limit = getLimit(region).get(index);
  if (!limit)
    return;

  var range = getRange(index);

  // Negative array index is not valid
  if (range.from < 0)
    return;

  // Index should be limited by array length
  if (limit.type !== '<' ||
      limit.value.opcode !== 'loadArrayLength' ||
      limit.value.inputs[0] !== array) {
    return;
  }

  // Check is safe to remove!
  reducer.remove(node);
}

var eliminateChecks = new Reducer.Reduction({
  reduce: function(node, reducer) {
    if (node.opcode === 'checkIndex')
      reduceCheckIndex(node, reducer);
  }
});
reduce(p, eliminateChecks);

//
// Run scheduler to put everything
// back to the CFG
//

var out = Scheduler.create(p).run();
out.reindex();

if (process.env.DEBUG)
  fs.writeFileSync('after.gv', out.render('graphviz'));

console.log(out.render({ cfg: true }, 'printable'));
