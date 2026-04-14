{
  description = "Riemann-Adelic Formal Verification - Lean 4 Proof Environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";
    lean4.url = "github:leanprover/lean4/v4.5.0";
  };

  outputs = { self, nixpkgs, flake-utils, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            lean4.packages.${system}.lean
            pkgs.gnumake
            pkgs.git
          ];

          shellHook = ''
            echo "Riemann-Adelic Lean 4 Proof Environment"
            echo "Lean version: $(lean --version)"
            echo ""
            echo "Run 'make proof' to build and verify formal proofs"
            echo "Run 'make help' for more options"
          '';
        };

        # Package for building the proof
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "riemann-adelic-proof";
          version = "5.1.0";
          src = ./.;

          buildInputs = [
            lean4.packages.${system}.lean
            pkgs.gnumake
          ];

          buildPhase = ''
            cd formalization/lean
            lake build
          '';

          installPhase = ''
            mkdir -p $out
            cp -r .lake $out/
          '';
        };
      }
    );
}
