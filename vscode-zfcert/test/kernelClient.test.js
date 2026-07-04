"use strict";

const assert = require("assert");
const path = require("path");
const {
  findProjectRoot,
  normalizeServerUrl,
  textThroughLine
} = require("../kernelClient");

assert.strictEqual(
  normalizeServerUrl("http://127.0.0.1:8099/"),
  "http://127.0.0.1:8099"
);
assert.strictEqual(textThroughLine("a\nb\nc", 0), "a");
assert.strictEqual(textThroughLine("a\nb\nc", 1), "a\nb");
assert.strictEqual(textThroughLine("a\nb\nc", 99), "a\nb\nc");
assert.throws(() => normalizeServerUrl("file:///tmp/kernel"));
assert.strictEqual(
  findProjectRoot(path.join(__dirname, "..", "..", "examples", "specialize.zfp")),
  path.resolve(__dirname, "..", "..")
);

console.log("kernelClient tests passed");
