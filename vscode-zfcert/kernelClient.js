"use strict";

const http = require("http");
const https = require("https");
const fs = require("fs");
const path = require("path");

function normalizeServerUrl(value) {
  const url = new URL(value);
  if (url.protocol !== "http:" && url.protocol !== "https:") {
    throw new Error("Kernel URL must use http or https");
  }
  return url.toString().replace(/\/$/, "");
}

function textThroughLine(text, line) {
  const lines = text.split(/\r?\n/);
  const last = Math.max(0, Math.min(line, lines.length - 1));
  return lines.slice(0, last + 1).join("\n");
}

function findProjectRoot(startPath) {
  if (!startPath) return undefined;
  let current = path.resolve(startPath);
  try {
    if (!fs.statSync(current).isDirectory()) current = path.dirname(current);
  } catch {
    current = path.dirname(current);
  }

  while (true) {
    if (fs.existsSync(path.join(current, "dune-project"))) return current;
    const parent = path.dirname(current);
    if (parent === current) return undefined;
    current = parent;
  }
}

class KernelClient {
  constructor(serverUrl, timeoutMs = 3000) {
    this.serverUrl = normalizeServerUrl(serverUrl);
    this.timeoutMs = timeoutMs;
  }

  request(method, path, body = "") {
    const target = new URL(path, `${this.serverUrl}/`);
    const transport = target.protocol === "https:" ? https : http;
    const payload = Buffer.from(body, "utf8");

    return new Promise((resolve, reject) => {
      const request = transport.request({
        protocol: target.protocol,
        hostname: target.hostname,
        port: target.port,
        path: `${target.pathname}${target.search}`,
        method,
        headers: {
          "Content-Type": "text/plain; charset=utf-8",
          "Content-Length": payload.length
        }
      }, (response) => {
        const chunks = [];
        response.on("data", (chunk) => chunks.push(chunk));
        response.on("end", () => {
          const text = Buffer.concat(chunks).toString("utf8");
          if (response.statusCode < 200 || response.statusCode >= 300) {
            reject(new Error(`Kernel returned HTTP ${response.statusCode}: ${text}`));
            return;
          }
          try {
            resolve(JSON.parse(text));
          } catch {
            reject(new Error(`Kernel returned invalid JSON: ${text}`));
          }
        });
      });

      request.setTimeout(this.timeoutMs, () => {
        request.destroy(new Error("Kernel request timed out"));
      });
      request.on("error", reject);
      if (payload.length > 0) request.write(payload);
      request.end();
    });
  }

  health() {
    return this.request("GET", "api/health");
  }

  step(script) {
    return this.request("POST", "api/step", script);
  }

  check(script) {
    return this.request("POST", "api/check", script);
  }
}

module.exports = {
  KernelClient,
  findProjectRoot,
  normalizeServerUrl,
  textThroughLine
};
