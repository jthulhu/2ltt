{
  description = "2LTT";
  
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    utils.url = "github:numtide/flake-utils";
  };
  
  outputs = { nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (final: prev: {
              lean4-git = final.lean4.overrideAttrs {
                version = "4.10.0";
                src = final.fetchFromGitHub {
                  owner = "leanprover";
                  repo = "lean4";
                  rev = "v4.10.0-rc1";
                  hash = "sha256-kB2cp1XJKODXiuiKp7J5OK+PFP+sOSBE5gdVNOKWCPI=";
                };
              };
            })
          ];
        };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            lean4-git
            elan
          ];
        };
    });
}
