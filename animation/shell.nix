let
  pkgs = import <nixpkgs> {};
in pkgs.mkShell {
  packages = with pkgs; [
    (manim.override { texliveInfraOnly = texliveInfraOnly.withPackages (ps: [ ps.bussproofs]); })
  ];
}
