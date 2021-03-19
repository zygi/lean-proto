{
  description = "LeanProto";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;

  inputs.lean.url = "path:../lean4";
  inputs.flake-utils.url = github:numtide/flake-utils;

  inputs.leanproto-native.url = "path:./native";
  inputs.leanproto-native.inputs.lean.follows = "lean";

  inputs.assrt-command.url = github:pnwamk/lean4-assert-command;
  inputs.assrt-command.inputs.lean.follows = "lean";

  outputs = { self, lean, flake-utils, leanproto-native, assrt-command, nixpkgs}: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "LeanProto";  # must match the name of the top-level .lean file
        src = ./.;
        deps = [leanproto-native.packages.${system} assrt-command.packages.${system}];
        pluginDeps = [leanproto-native.packages.${system}.sharedLib];
        staticLibDeps = [leanproto-native.packages.${system}.staticLib];
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}

