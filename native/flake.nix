{
  description = "LeanProto";

  inputs.nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
  inputs.nix.url = github:NixOS/nix;

  inputs.lean.url = "github:leanprover/lean4";
  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = { self, lean, flake-utils, nixpkgs, nix}: flake-utils.lib.eachDefaultSystem (system:
    let
      cPkg = with import nixpkgs { inherit system; };
        stdenv.mkDerivation rec {
          buildInputs = [glibc.static lean.packages.${system}.leanc];
          name = "libLeanProtoNativeHelpersC.a";
          src = ./helpers.c;
          dontUnpack = true;
          buildPhase =
            "leanc -fPIC -c -o out.o ${src}; ar rcs ${name} *.o";
          installPhase = "mkdir -p $out; install -t $out ${name}";
        };
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "LeanProtoNativeHelpers";  # must match the name of the top-level .lean file
        src = ./.;
        staticLibDeps = [cPkg];
        # deps = [];
        # deps = [ lean.packages.${system}.Init ];
      };
    in {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}

