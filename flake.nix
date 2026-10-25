{
  description = "nano-lean";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      nixpkgs,
      rust-overlay,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import rust-overlay) ];
        };
        # Pinned by rust-toolchain.toml, which CI's dtolnay/rust-toolchain matches.
        rustToolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            (rustToolchain.override {
              extensions = [
                "rust-src"
                "rust-analyzer"
              ];
            })
            pkgs.pre-commit
            # The Lean corpora (.github/scripts/mathlib-ci.sh): elan fetches
            # each downstream project's pinned toolchain, python3 checks the
            # exports and reports.
            pkgs.elan
            pkgs.python3
          ];
        };
      }
    );
}
