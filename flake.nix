{
  description = "LeanProto";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;

  inputs.lean.url = github:leanprover/lean4;
  inputs.flake-utils.url = github:numtide/flake-utils;

  inputs.assrt-command.url = github:pnwamk/lean4-assert-command;
  inputs.assrt-command.inputs.lean.follows = "lean";

  outputs = { self, lean, flake-utils, assrt-command, nixpkgs}: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      
      nativeCPkg = with import nixpkgs { inherit system; };
        stdenv.mkDerivation rec {
          buildInputs = [glibc.static lean.packages.${system}.leanc];
          name = "libLeanProtoNativeHelpersC.a";
          src = ./native/helpers.c;
          dontUnpack = true;
          buildPhase =
            "leanc -fPIC -c -o out.o ${src}; ar rcs ${name} *.o";
          installPhase = "mkdir -p $out; install -t $out ${name}";
        };

      nativePkg = leanPkgs.buildLeanPackage {
        name = "LeanProtoNativeHelpers";  # must match the name of the top-level .lean file
        src = ./native;
        staticLibDeps = [nativeCPkg];
      };

      pkg = leanPkgs.buildLeanPackage {
        name = "LeanProto";  # must match the name of the top-level .lean file
        src = ./.;
        deps = [nativePkg assrt-command.packages.${system}];
        pluginDeps = [nativePkg.sharedLib];
        staticLibDeps = [nativePkg.staticLib];
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}

