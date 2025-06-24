{ flake, ... }:
final: prev: {
  haskellPackages = prev.haskellPackages.override (old: {
    overrides = prev.lib.composeExtensions (old.overrides or (_: _: { })) (
      hself: hsuper: {
        inherit (prev.labHaskellPackages) Agda;
      }
    );
  });

  agdaPackages = prev.agdaPackages.overrideScope (
    self: superAgda: {
      _1lab = superAgda._1lab.overrideAttrs (
        oldAttrs:
        let
          inherit (prev.lib.strings) concatMapStrings;
          includePathArgs = concatMapStrings (path: "-i " + path + " ") [ (dirOf oldAttrs.everythingFile) ];
        in
        {
          src = "${flake}";
          version = "unstable";
          nativeBuildInputs = [ prev.strace ];
          buildPhase = ''
            runHook preBuild
            mkdir ./datadir
            Agda_datadir=./datadir agda ${oldAttrs.everythingFile} ${includePathArgs}
            rm -r ./datadir ${oldAttrs.everythingFile} ${final.agdaPackages.agda.version}
            runHook postBuild
          '';
        }
      );
    }
  );
}
