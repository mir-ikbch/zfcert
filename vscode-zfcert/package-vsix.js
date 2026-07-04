"use strict";

const fs = require("fs");
const os = require("os");
const path = require("path");
const childProcess = require("child_process");

const root = __dirname;
const pkg = require("./package.json");
const output = path.resolve(root, "..", `zfcert-vscode-${pkg.version}.vsix`);
const staging = fs.mkdtempSync(path.join(os.tmpdir(), "zfcert-vsix-"));
const extensionRoot = path.join(staging, "extension");

function copy(relative) {
  const source = path.join(root, relative);
  const destination = path.join(extensionRoot, relative);
  fs.mkdirSync(path.dirname(destination), { recursive: true });
  fs.cpSync(source, destination, { recursive: true });
}

function xml(value) {
  return String(value)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

try {
  [
    "package.json",
    "README.md",
    "extension.js",
    "kernelClient.js",
    "language-configuration.json",
    "syntaxes",
    "snippets",
    "media"
  ].forEach(copy);

  const manifest = `<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0"
  xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011">
  <Metadata>
    <Identity Language="en-US" Id="${xml(pkg.name)}"
      Version="${xml(pkg.version)}" Publisher="${xml(pkg.publisher)}" />
    <DisplayName>${xml(pkg.displayName)}</DisplayName>
    <Description xml:space="preserve">${xml(pkg.description)}</Description>
    <Tags>${xml((pkg.keywords || []).join(","))}</Tags>
    <Categories>${xml((pkg.categories || []).join(","))}</Categories>
    <Properties>
      <Property Id="Microsoft.VisualStudio.Code.Engine"
        Value="${xml(pkg.engines.vscode)}" />
      <Property Id="Microsoft.VisualStudio.Code.ExtensionKind"
        Value="workspace" />
    </Properties>
  </Metadata>
  <Installation>
    <InstallationTarget Id="Microsoft.VisualStudio.Code" />
  </Installation>
  <Dependencies />
  <Assets>
    <Asset Type="Microsoft.VisualStudio.Code.Manifest"
      Path="extension/package.json" Addressable="true" />
    <Asset Type="Microsoft.VisualStudio.Services.Content.Details"
      Path="extension/README.md" Addressable="true" />
  </Assets>
</PackageManifest>
`;
  fs.writeFileSync(path.join(staging, "extension.vsixmanifest"), manifest);

  const contentTypes = `<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="json" ContentType="application/json" />
  <Default Extension="js" ContentType="application/javascript" />
  <Default Extension="md" ContentType="text/markdown" />
  <Default Extension="svg" ContentType="image/svg+xml" />
  <Override PartName="/extension.vsixmanifest" ContentType="text/xml" />
</Types>
`;
  fs.writeFileSync(path.join(staging, "[Content_Types].xml"), contentTypes);

  fs.rmSync(output, { force: true });
  const zip = childProcess.spawnSync(
    "zip",
    ["-qr", output, "[Content_Types].xml", "extension.vsixmanifest", "extension"],
    { cwd: staging, stdio: "inherit" }
  );
  if (zip.status !== 0) throw new Error("zip failed");
  console.log(`Created ${output}`);
} finally {
  fs.rmSync(staging, { recursive: true, force: true });
}
