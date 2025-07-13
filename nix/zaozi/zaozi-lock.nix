{ fetchurl }:
let
  fetchMaven = { name, urls, hash, installPath }: with builtins;
    let
      firstUrl = head urls;
      otherUrls = filter (elem: elem != firstUrl) urls;
    in
    fetchurl {
      inherit name hash;
      passthru = { inherit installPath; };
      url = firstUrl;
      recursiveHash = true;
      downloadToTemp = true;
      postFetch = ''
        mkdir -p "$out"
        cp -v "$downloadedFile" "$out/${baseNameOf firstUrl}"
      '' + concatStringsSep "\n"
        (map
          (elem:
            let filename = baseNameOf elem; in ''
              downloadedFile=$TMPDIR/${filename}
              tryDownload ${elem}
              cp -v "$TMPDIR/${filename}" "$out/"
            '')
          otherUrls);
    };
in
{

  "commons-codec_commons-codec-1.17.0" = fetchMaven {
    name = "commons-codec_commons-codec-1.17.0";
    urls = [ "https://repo1.maven.org/maven2/commons-codec/commons-codec/1.17.0/commons-codec-1.17.0.jar" "https://repo1.maven.org/maven2/commons-codec/commons-codec/1.17.0/commons-codec-1.17.0.pom" ];
    hash = "sha256-rNXCmSoMZ3Hx493sMGpc4SCAgPOJ8TBZNlPtmFMGw5M=";
    installPath = "https/repo1.maven.org/maven2/commons-codec/commons-codec/1.17.0";
  };

  "commons-io_commons-io-2.18.0" = fetchMaven {
    name = "commons-io_commons-io-2.18.0";
    urls = [ "https://repo1.maven.org/maven2/commons-io/commons-io/2.18.0/commons-io-2.18.0.jar" "https://repo1.maven.org/maven2/commons-io/commons-io/2.18.0/commons-io-2.18.0.pom" ];
    hash = "sha256-VrNF9aYN/xZddMiPVnJgXu9Pbv3leLTX+h31aBWzEUY=";
    installPath = "https/repo1.maven.org/maven2/commons-io/commons-io/2.18.0";
  };

  "com.eed3si9n_shaded-jawn-parser_2.13-1.3.2" = fetchMaven {
    name = "com.eed3si9n_shaded-jawn-parser_2.13-1.3.2";
    urls = [ "https://repo1.maven.org/maven2/com/eed3si9n/shaded-jawn-parser_2.13/1.3.2/shaded-jawn-parser_2.13-1.3.2.jar" "https://repo1.maven.org/maven2/com/eed3si9n/shaded-jawn-parser_2.13/1.3.2/shaded-jawn-parser_2.13-1.3.2.pom" ];
    hash = "sha256-k0UsS5J5CXho/H4FngEcxAkNJ2ZjpecqDmKBvxIMuBs=";
    installPath = "https/repo1.maven.org/maven2/com/eed3si9n/shaded-jawn-parser_2.13/1.3.2";
  };

  "com.eed3si9n_shaded-scalajson_2.13-1.0.0-M4" = fetchMaven {
    name = "com.eed3si9n_shaded-scalajson_2.13-1.0.0-M4";
    urls = [ "https://repo1.maven.org/maven2/com/eed3si9n/shaded-scalajson_2.13/1.0.0-M4/shaded-scalajson_2.13-1.0.0-M4.jar" "https://repo1.maven.org/maven2/com/eed3si9n/shaded-scalajson_2.13/1.0.0-M4/shaded-scalajson_2.13-1.0.0-M4.pom" ];
    hash = "sha256-JyvPek41KleFIS5g4bqLm+qUw5FlX51/rnvv/BT2pk0=";
    installPath = "https/repo1.maven.org/maven2/com/eed3si9n/shaded-scalajson_2.13/1.0.0-M4";
  };

  "com.eed3si9n_sjson-new-core_2.13-0.10.1" = fetchMaven {
    name = "com.eed3si9n_sjson-new-core_2.13-0.10.1";
    urls = [ "https://repo1.maven.org/maven2/com/eed3si9n/sjson-new-core_2.13/0.10.1/sjson-new-core_2.13-0.10.1.jar" "https://repo1.maven.org/maven2/com/eed3si9n/sjson-new-core_2.13/0.10.1/sjson-new-core_2.13-0.10.1.pom" ];
    hash = "sha256-sFHoDAQBTHju2EgUOPuO9tM/SLAdb8X/oNSnar0iYoQ=";
    installPath = "https/repo1.maven.org/maven2/com/eed3si9n/sjson-new-core_2.13/0.10.1";
  };

  "com.eed3si9n_sjson-new-core_2.13-0.9.0" = fetchMaven {
    name = "com.eed3si9n_sjson-new-core_2.13-0.9.0";
    urls = [ "https://repo1.maven.org/maven2/com/eed3si9n/sjson-new-core_2.13/0.9.0/sjson-new-core_2.13-0.9.0.pom" ];
    hash = "sha256-WlJsXRKj77jzoFN6d1V/+jAEl37mxggg85F3o8oD+bY=";
    installPath = "https/repo1.maven.org/maven2/com/eed3si9n/sjson-new-core_2.13/0.9.0";
  };

  "com.eed3si9n_sjson-new-scalajson_2.13-0.10.1" = fetchMaven {
    name = "com.eed3si9n_sjson-new-scalajson_2.13-0.10.1";
    urls = [ "https://repo1.maven.org/maven2/com/eed3si9n/sjson-new-scalajson_2.13/0.10.1/sjson-new-scalajson_2.13-0.10.1.jar" "https://repo1.maven.org/maven2/com/eed3si9n/sjson-new-scalajson_2.13/0.10.1/sjson-new-scalajson_2.13-0.10.1.pom" ];
    hash = "sha256-DBGJ34c7lyt3m4o5ULwsRk1xPqtHHHKcNgU4nlO/dJY=";
    installPath = "https/repo1.maven.org/maven2/com/eed3si9n/sjson-new-scalajson_2.13/0.10.1";
  };

  "com.fasterxml_oss-parent-41" = fetchMaven {
    name = "com.fasterxml_oss-parent-41";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/oss-parent/41/oss-parent-41.pom" ];
    hash = "sha256-Lz63NGj0J8xjePtb7p69ACd08meStmdjmgtoh9zp2tQ=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/oss-parent/41";
  };

  "com.fasterxml_oss-parent-50" = fetchMaven {
    name = "com.fasterxml_oss-parent-50";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/oss-parent/50/oss-parent-50.pom" ];
    hash = "sha256-2z6+ukMOEKSrgEACAV2Qo5AF5bBFbMhoZVekS4VelPQ=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/oss-parent/50";
  };

  "com.fasterxml_oss-parent-58" = fetchMaven {
    name = "com.fasterxml_oss-parent-58";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/oss-parent/58/oss-parent-58.pom" ];
    hash = "sha256-wVCyn9u4Q5PMWSigrfRD2c90jacWbffIBxjXZq/VOSw=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/oss-parent/58";
  };

  "com.fasterxml_oss-parent-61" = fetchMaven {
    name = "com.fasterxml_oss-parent-61";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/oss-parent/61/oss-parent-61.pom" ];
    hash = "sha256-lZ8EM5Hz6HV9EYjiL2vc9lP5ORQVR/utOZ5Dc18O6TA=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/oss-parent/61";
  };

  "com.lihaoyi_fansi_3-0.5.0" = fetchMaven {
    name = "com.lihaoyi_fansi_3-0.5.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/fansi_3/0.5.0/fansi_3-0.5.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/fansi_3/0.5.0/fansi_3-0.5.0.pom" ];
    hash = "sha256-LBJpOQv1O5lM5QVBMp4to7u3N8dCmqg/lxEi6mVmgPo=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/fansi_3/0.5.0";
  };

  "com.lihaoyi_fastparse_3-3.1.1" = fetchMaven {
    name = "com.lihaoyi_fastparse_3-3.1.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/fastparse_3/3.1.1/fastparse_3-3.1.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/fastparse_3/3.1.1/fastparse_3-3.1.1.pom" ];
    hash = "sha256-iz6Wj92asaujz93RjmBAaKHHV64HS26cduPsQzaD6wM=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/fastparse_3/3.1.1";
  };

  "com.lihaoyi_geny_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_geny_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/geny_3/1.0.0/geny_3-1.0.0.pom" ];
    hash = "sha256-gyZV3FMH1nlWfPJ0nAN3y08zzWtW4AYPo1A3oaMraUY=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/geny_3/1.0.0";
  };

  "com.lihaoyi_geny_3-1.1.1" = fetchMaven {
    name = "com.lihaoyi_geny_3-1.1.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/geny_3/1.1.1/geny_3-1.1.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/geny_3/1.1.1/geny_3-1.1.1.pom" ];
    hash = "sha256-DtsM1VVr7WxRM+YRjjVDOkfCqXzp2q9FwlSMgoD/+ow=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/geny_3/1.1.1";
  };

  "com.lihaoyi_mainargs_3-0.7.6" = fetchMaven {
    name = "com.lihaoyi_mainargs_3-0.7.6";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mainargs_3/0.7.6/mainargs_3-0.7.6.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mainargs_3/0.7.6/mainargs_3-0.7.6.pom" ];
    hash = "sha256-d0HGGb6XHh0K8gP9Y0gSt1pbUhMPoI/WBJSOll5ZywE=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mainargs_3/0.7.6";
  };

  "com.lihaoyi_mill-contrib-jmh_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-contrib-jmh_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-contrib-jmh_3/1.0.0/mill-contrib-jmh_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-contrib-jmh_3/1.0.0/mill-contrib-jmh_3-1.0.0.pom" ];
    hash = "sha256-8P/O8cq4oY1t9KTjVRY3DcO0Y8mRtP2rTMo5/ISSANc=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-contrib-jmh_3/1.0.0";
  };

  "com.lihaoyi_mill-core-api-daemon_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-api-daemon_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-api-daemon_3/1.0.0/mill-core-api-daemon_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-api-daemon_3/1.0.0/mill-core-api-daemon_3-1.0.0.pom" ];
    hash = "sha256-i+s0nVb0j/Q4qvLC+9jVcDMfX7mjArh/7CRBr6A188g=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-api-daemon_3/1.0.0";
  };

  "com.lihaoyi_mill-core-api_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-api_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-api_3/1.0.0/mill-core-api_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-api_3/1.0.0/mill-core-api_3-1.0.0.pom" ];
    hash = "sha256-u2C5HLfIoBC2vs1itN+4H3epzGAu6w8QNpz/n8rxn5A=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-api_3/1.0.0";
  };

  "com.lihaoyi_mill-core-constants-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-constants-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-constants/1.0.0/mill-core-constants-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-constants/1.0.0/mill-core-constants-1.0.0.pom" ];
    hash = "sha256-TCRuKrXWSFMXLaQrT+Ecj1PAk+C1mf1uZN37VjS4G+4=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-constants/1.0.0";
  };

  "com.lihaoyi_mill-core-coursierutil_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-coursierutil_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-coursierutil_3/1.0.0/mill-core-coursierutil_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-coursierutil_3/1.0.0/mill-core-coursierutil_3-1.0.0.pom" ];
    hash = "sha256-ZVSDkaWGVumIQp60Ph0IDXY2Xxhu5HUAZimCR8GRe80=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-coursierutil_3/1.0.0";
  };

  "com.lihaoyi_mill-core-eval_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-eval_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-eval_3/1.0.0/mill-core-eval_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-eval_3/1.0.0/mill-core-eval_3-1.0.0.pom" ];
    hash = "sha256-8+BNfOd8FcyiVtXEx/uzb/1KYbxyJCGgHhqf0tO+pNs=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-eval_3/1.0.0";
  };

  "com.lihaoyi_mill-core-exec_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-exec_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-exec_3/1.0.0/mill-core-exec_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-exec_3/1.0.0/mill-core-exec_3-1.0.0.pom" ];
    hash = "sha256-tlxaFzyo+HFvrSkFh3hBd4JzUvNfuYZS59jaxBn8uF4=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-exec_3/1.0.0";
  };

  "com.lihaoyi_mill-core-internal_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-internal_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-internal_3/1.0.0/mill-core-internal_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-internal_3/1.0.0/mill-core-internal_3-1.0.0.pom" ];
    hash = "sha256-7wUKxkbfrtDV/sQWBVOoJd3rgBiUtYFHsE0x9ysjYek=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-internal_3/1.0.0";
  };

  "com.lihaoyi_mill-core-resolve_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-core-resolve_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-resolve_3/1.0.0/mill-core-resolve_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-core-resolve_3/1.0.0/mill-core-resolve_3-1.0.0.pom" ];
    hash = "sha256-+3rL1GQJKD2uE2mp+cWEBGuFhKctiDtYHGKlwIZHYAg=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-core-resolve_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-androidlib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-androidlib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-androidlib_3/1.0.0/mill-libs-androidlib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-androidlib_3/1.0.0/mill-libs-androidlib_3-1.0.0.pom" ];
    hash = "sha256-ux19cT1H2JVi4A/NrKIG5dE0JYGnu/c5jx0oQeIGdUI=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-androidlib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-init_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-init_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-init_3/1.0.0/mill-libs-init_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-init_3/1.0.0/mill-libs-init_3-1.0.0.pom" ];
    hash = "sha256-1IL+XiYdpIXfwfZD3J9eEzk0fc1p6jPKH1AUK5GGdfc=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-init_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-javalib-api_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javalib-api_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-api_3/1.0.0/mill-libs-javalib-api_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-api_3/1.0.0/mill-libs-javalib-api_3-1.0.0.pom" ];
    hash = "sha256-7TjZSlLKHsIBRUntKezdnng7d/lCJRnobzXJo1+uop0=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-api_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-javalib-classgraph-worker_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javalib-classgraph-worker_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-classgraph-worker_3/1.0.0/mill-libs-javalib-classgraph-worker_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-classgraph-worker_3/1.0.0/mill-libs-javalib-classgraph-worker_3-1.0.0.pom" ];
    hash = "sha256-u3TJcZSymcVwCixHg42TzdBOaST0krs+s7Nx1Io9K2w=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-classgraph-worker_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-javalib-testrunner-entrypoint-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javalib-testrunner-entrypoint-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-testrunner-entrypoint/1.0.0/mill-libs-javalib-testrunner-entrypoint-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-testrunner-entrypoint/1.0.0/mill-libs-javalib-testrunner-entrypoint-1.0.0.pom" ];
    hash = "sha256-eY7jwyZUVl29ETPGNrMRQzPJ2cZXaUduQn2pVsVoprA=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-testrunner-entrypoint/1.0.0";
  };

  "com.lihaoyi_mill-libs-javalib-testrunner_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javalib-testrunner_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-testrunner_3/1.0.0/mill-libs-javalib-testrunner_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-testrunner_3/1.0.0/mill-libs-javalib-testrunner_3-1.0.0.pom" ];
    hash = "sha256-3F9qFfbRy5r1ISuZ6eqQEMhvr0zc4rSq3kddsaS0f60=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-testrunner_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-javalib-worker_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javalib-worker_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-worker_3/1.0.0/mill-libs-javalib-worker_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-worker_3/1.0.0/mill-libs-javalib-worker_3-1.0.0.pom" ];
    hash = "sha256-Daw/C/uSbUWtWZ5cuKcmdBNOu6ebpKREJh6VfQoyVaU=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib-worker_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-javalib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javalib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib_3/1.0.0/mill-libs-javalib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib_3/1.0.0/mill-libs-javalib_3-1.0.0.pom" ];
    hash = "sha256-Vzv9aT7R2u0AkVS71SwX4l3rlqtqQ6TD0rJgmgOU4VY=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javalib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-javascriptlib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-javascriptlib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javascriptlib_3/1.0.0/mill-libs-javascriptlib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-javascriptlib_3/1.0.0/mill-libs-javascriptlib_3-1.0.0.pom" ];
    hash = "sha256-GTKnjziEm/V61g8G76u2aAxnYa1S5waGXRQblSFS9jg=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-javascriptlib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-kotlinlib-api_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-kotlinlib-api_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-kotlinlib-api_3/1.0.0/mill-libs-kotlinlib-api_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-kotlinlib-api_3/1.0.0/mill-libs-kotlinlib-api_3-1.0.0.pom" ];
    hash = "sha256-PCD6FTYIOC2/a8j6UwLcJ9E/8kJjGs8531+ZjXUl5WA=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-kotlinlib-api_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-kotlinlib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-kotlinlib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-kotlinlib_3/1.0.0/mill-libs-kotlinlib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-kotlinlib_3/1.0.0/mill-libs-kotlinlib_3-1.0.0.pom" ];
    hash = "sha256-dxulxT/zrVC3NhbjXDQGO1vJCAXlKo4wIekKuI40HO4=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-kotlinlib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-pythonlib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-pythonlib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-pythonlib_3/1.0.0/mill-libs-pythonlib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-pythonlib_3/1.0.0/mill-libs-pythonlib_3-1.0.0.pom" ];
    hash = "sha256-hSZsibPqMgxfyGbh7Xc/DDQifo9vqV40NWJuiREC0B4=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-pythonlib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-scalajslib-api_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-scalajslib-api_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalajslib-api_3/1.0.0/mill-libs-scalajslib-api_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalajslib-api_3/1.0.0/mill-libs-scalajslib-api_3-1.0.0.pom" ];
    hash = "sha256-BsE3g4Y21DTdBVigdvqt+EKj+/ceFPGE98Te4qud9tg=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalajslib-api_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-scalajslib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-scalajslib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalajslib_3/1.0.0/mill-libs-scalajslib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalajslib_3/1.0.0/mill-libs-scalajslib_3-1.0.0.pom" ];
    hash = "sha256-1Nm5x9uL0z3cTqDQj1RVXYMGvefGyZ7du/yILQwFfzA=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalajslib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-scalalib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-scalalib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalalib_3/1.0.0/mill-libs-scalalib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalalib_3/1.0.0/mill-libs-scalalib_3-1.0.0.pom" ];
    hash = "sha256-uhBgwJiNIXF1DQfXX86yBngkFeDlnXcMwbiJ2+x5zr8=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalalib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-scalanativelib-api_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-scalanativelib-api_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalanativelib-api_3/1.0.0/mill-libs-scalanativelib-api_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalanativelib-api_3/1.0.0/mill-libs-scalanativelib-api_3-1.0.0.pom" ];
    hash = "sha256-9kwy9SI0TJI3vbGiot/W3114uzyyHQfiHEabKtTeBxQ=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalanativelib-api_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-scalanativelib_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-scalanativelib_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalanativelib_3/1.0.0/mill-libs-scalanativelib_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalanativelib_3/1.0.0/mill-libs-scalanativelib_3-1.0.0.pom" ];
    hash = "sha256-NoNgoymYlGKNNA6VbCMmI2+tcCn7l1ORFaET4yLTBlY=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-scalanativelib_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-tabcomplete_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-tabcomplete_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-tabcomplete_3/1.0.0/mill-libs-tabcomplete_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-tabcomplete_3/1.0.0/mill-libs-tabcomplete_3-1.0.0.pom" ];
    hash = "sha256-qf1wDvPdID+1vNTyNhzzc4EMFn8DSc9hIFJ45TcyEzQ=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-tabcomplete_3/1.0.0";
  };

  "com.lihaoyi_mill-libs-util_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs-util_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-util_3/1.0.0/mill-libs-util_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs-util_3/1.0.0/mill-libs-util_3-1.0.0.pom" ];
    hash = "sha256-G3uRQ/3prkGAV7h3lDnNHfc2Tv/tV3sukqv9AnUoLXo=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs-util_3/1.0.0";
  };

  "com.lihaoyi_mill-libs_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-libs_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs_3/1.0.0/mill-libs_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-libs_3/1.0.0/mill-libs_3-1.0.0.pom" ];
    hash = "sha256-+0G57Cjr0YQ66Tp45MTUxe9k88mj4QMHFM/uo/3l/OA=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-libs_3/1.0.0";
  };

  "com.lihaoyi_mill-moduledefs_3-0.11.10" = fetchMaven {
    name = "com.lihaoyi_mill-moduledefs_3-0.11.10";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-moduledefs_3/0.11.10/mill-moduledefs_3-0.11.10.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-moduledefs_3/0.11.10/mill-moduledefs_3-0.11.10.pom" ];
    hash = "sha256-3FdBfiXAHCjX8Pz84XHV6mkCb0q5TLWUT7ADflSeVW0=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-moduledefs_3/0.11.10";
  };

  "com.lihaoyi_mill-runner-bsp-worker_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-bsp-worker_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-bsp-worker_3/1.0.0/mill-runner-bsp-worker_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-bsp-worker_3/1.0.0/mill-runner-bsp-worker_3-1.0.0.pom" ];
    hash = "sha256-7eauXgyWmnwFtkR4yeSR4X/4KsXeXTjFDQxqfPGj2/Y=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-bsp-worker_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-bsp_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-bsp_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-bsp_3/1.0.0/mill-runner-bsp_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-bsp_3/1.0.0/mill-runner-bsp_3-1.0.0.pom" ];
    hash = "sha256-6vuvvrR/Nrp1elHi2Zot5ejMhmsSv2A27Vnw42IQYPY=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-bsp_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-client-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-client-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-client/1.0.0/mill-runner-client-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-client/1.0.0/mill-runner-client-1.0.0.pom" ];
    hash = "sha256-BvPk8PBCXAbiHlRQXof5VjCr5FIBqd+dKnltiDkvngw=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-client/1.0.0";
  };

  "com.lihaoyi_mill-runner-codesig_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-codesig_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-codesig_3/1.0.0/mill-runner-codesig_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-codesig_3/1.0.0/mill-runner-codesig_3-1.0.0.pom" ];
    hash = "sha256-BrJwWKo0P0GC39i7lhIOFrk32gljdq8qSfnqOJO51Mc=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-codesig_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-daemon_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-daemon_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-daemon_3/1.0.0/mill-runner-daemon_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-daemon_3/1.0.0/mill-runner-daemon_3-1.0.0.pom" ];
    hash = "sha256-UmiO0PgSHcCHIg4HM1XdkllaY6Bm6yGOrNbmIVt2K1s=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-daemon_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-idea_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-idea_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-idea_3/1.0.0/mill-runner-idea_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-idea_3/1.0.0/mill-runner-idea_3-1.0.0.pom" ];
    hash = "sha256-o/t/IAbv7mbmT9mT3bZkxOMxN3eqMDJ5aQVNc5hpgsI=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-idea_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-launcher_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-launcher_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-launcher_3/1.0.0/mill-runner-launcher_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-launcher_3/1.0.0/mill-runner-launcher_3-1.0.0.pom" ];
    hash = "sha256-RqYPSDjw+z/z2X1gsaxXDRBTTemZR//JS8J6KQW1C7Y=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-launcher_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-meta_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-meta_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-meta_3/1.0.0/mill-runner-meta_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-meta_3/1.0.0/mill-runner-meta_3-1.0.0.pom" ];
    hash = "sha256-J/RO2Tnk1SnjQDw+GMjl5xFjlmrshdjJpxTODd6CZ6A=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-meta_3/1.0.0";
  };

  "com.lihaoyi_mill-runner-server_3-1.0.0" = fetchMaven {
    name = "com.lihaoyi_mill-runner-server_3-1.0.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-server_3/1.0.0/mill-runner-server_3-1.0.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/mill-runner-server_3/1.0.0/mill-runner-server_3-1.0.0.pom" ];
    hash = "sha256-rrIvqVubqPeMRzjYCPtOVAlmvrS+B56LMd+DWR8HEIA=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/mill-runner-server_3/1.0.0";
  };

  "com.lihaoyi_os-lib-watch_3-0.11.5-M10" = fetchMaven {
    name = "com.lihaoyi_os-lib-watch_3-0.11.5-M10";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/os-lib-watch_3/0.11.5-M10/os-lib-watch_3-0.11.5-M10.jar" "https://repo1.maven.org/maven2/com/lihaoyi/os-lib-watch_3/0.11.5-M10/os-lib-watch_3-0.11.5-M10.pom" ];
    hash = "sha256-DsZ/d3atXTBrHOABv9ohB96v0cn80ehyPQcsgiPN52w=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/os-lib-watch_3/0.11.5-M10";
  };

  "com.lihaoyi_os-lib_3-0.11.3" = fetchMaven {
    name = "com.lihaoyi_os-lib_3-0.11.3";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/os-lib_3/0.11.3/os-lib_3-0.11.3.jar" "https://repo1.maven.org/maven2/com/lihaoyi/os-lib_3/0.11.3/os-lib_3-0.11.3.pom" ];
    hash = "sha256-oNCL91uzMsZR4hsuDStMx80VtqvudIKLv3Z92Izhnac=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/os-lib_3/0.11.3";
  };

  "com.lihaoyi_os-lib_3-0.11.5-M10" = fetchMaven {
    name = "com.lihaoyi_os-lib_3-0.11.5-M10";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/os-lib_3/0.11.5-M10/os-lib_3-0.11.5-M10.jar" "https://repo1.maven.org/maven2/com/lihaoyi/os-lib_3/0.11.5-M10/os-lib_3-0.11.5-M10.pom" ];
    hash = "sha256-ikBN7Omg6zBHiLTihyky5F1d0Sa8aZy7lmpIlI0eEWs=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/os-lib_3/0.11.5-M10";
  };

  "com.lihaoyi_os-zip-0.11.5-M10" = fetchMaven {
    name = "com.lihaoyi_os-zip-0.11.5-M10";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/os-zip/0.11.5-M10/os-zip-0.11.5-M10.jar" "https://repo1.maven.org/maven2/com/lihaoyi/os-zip/0.11.5-M10/os-zip-0.11.5-M10.pom" ];
    hash = "sha256-cROEwjbluffNKwBpfxDa/QIFnk+hBKppxV4KcynoHjE=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/os-zip/0.11.5-M10";
  };

  "com.lihaoyi_pprint_3-0.9.0" = fetchMaven {
    name = "com.lihaoyi_pprint_3-0.9.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/pprint_3/0.9.0/pprint_3-0.9.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/pprint_3/0.9.0/pprint_3-0.9.0.pom" ];
    hash = "sha256-G9+cXrjL/+aawfpe5/xSRzxGiyYWUGKyE1G2sPKHwOk=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/pprint_3/0.9.0";
  };

  "com.lihaoyi_requests_3-0.9.0" = fetchMaven {
    name = "com.lihaoyi_requests_3-0.9.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/requests_3/0.9.0/requests_3-0.9.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/requests_3/0.9.0/requests_3-0.9.0.pom" ];
    hash = "sha256-ueGLE6/p3TelKviK8v0F1xJShdQfoSHGQoLT58/xf94=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/requests_3/0.9.0";
  };

  "com.lihaoyi_scalac-mill-moduledefs-plugin_3.7.1-0.11.10" = fetchMaven {
    name = "com.lihaoyi_scalac-mill-moduledefs-plugin_3.7.1-0.11.10";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/scalac-mill-moduledefs-plugin_3.7.1/0.11.10/scalac-mill-moduledefs-plugin_3.7.1-0.11.10.jar" "https://repo1.maven.org/maven2/com/lihaoyi/scalac-mill-moduledefs-plugin_3.7.1/0.11.10/scalac-mill-moduledefs-plugin_3.7.1-0.11.10.pom" ];
    hash = "sha256-gpq+NNC+zfHIixQIsLpSuNV8OifbsWcayVkOJlVcRVI=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/scalac-mill-moduledefs-plugin_3.7.1/0.11.10";
  };

  "com.lihaoyi_sourcecode_2.13-0.4.2" = fetchMaven {
    name = "com.lihaoyi_sourcecode_2.13-0.4.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_2.13/0.4.2/sourcecode_2.13-0.4.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_2.13/0.4.2/sourcecode_2.13-0.4.2.pom" ];
    hash = "sha256-DHoOpFdNH5fiJeRdm4A49d+SZpdp+iIeN7Po7oXz00g=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/sourcecode_2.13/0.4.2";
  };

  "com.lihaoyi_sourcecode_3-0.3.0" = fetchMaven {
    name = "com.lihaoyi_sourcecode_3-0.3.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.3.0/sourcecode_3-0.3.0.pom" ];
    hash = "sha256-lr4/nfVXauGgxI2rR6IJs2lPSQkS39mb8QS//1agWtA=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.3.0";
  };

  "com.lihaoyi_sourcecode_3-0.4.0" = fetchMaven {
    name = "com.lihaoyi_sourcecode_3-0.4.0";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.0/sourcecode_3-0.4.0.jar" "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.0/sourcecode_3-0.4.0.pom" ];
    hash = "sha256-uuL36U8SXTZ1e0obeznF/zJXAspEWrmdYzOTgfrhMto=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.0";
  };

  "com.lihaoyi_sourcecode_3-0.4.2" = fetchMaven {
    name = "com.lihaoyi_sourcecode_3-0.4.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.2/sourcecode_3-0.4.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.2/sourcecode_3-0.4.2.pom" ];
    hash = "sha256-p5LcBw7u9P3PAtUq5nbl4GN7P59H9EdAI9rwbLr1P4Y=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.2";
  };

  "com.lihaoyi_sourcecode_3-0.4.3-M5" = fetchMaven {
    name = "com.lihaoyi_sourcecode_3-0.4.3-M5";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.3-M5/sourcecode_3-0.4.3-M5.jar" "https://repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.3-M5/sourcecode_3-0.4.3-M5.pom" ];
    hash = "sha256-4W9BOcVHjFFDJgvePBp2NOvFQMMuHIlq2YXpctVpWqg=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/sourcecode_3/0.4.3-M5";
  };

  "com.lihaoyi_ujson_3-4.0.2" = fetchMaven {
    name = "com.lihaoyi_ujson_3-4.0.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/ujson_3/4.0.2/ujson_3-4.0.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/ujson_3/4.0.2/ujson_3-4.0.2.pom" ];
    hash = "sha256-sh595bxDgPH+K/tgqyzxgMrwafXDlYep4ScqZ5dcwI8=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/ujson_3/4.0.2";
  };

  "com.lihaoyi_ujson_3-4.2.1" = fetchMaven {
    name = "com.lihaoyi_ujson_3-4.2.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/ujson_3/4.2.1/ujson_3-4.2.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/ujson_3/4.2.1/ujson_3-4.2.1.pom" ];
    hash = "sha256-fOh8LRF0pFUVxrTu+Lxc4MLoEvRiUQxkTiJpYQiREyc=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/ujson_3/4.2.1";
  };

  "com.lihaoyi_upack_3-4.0.2" = fetchMaven {
    name = "com.lihaoyi_upack_3-4.0.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upack_3/4.0.2/upack_3-4.0.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upack_3/4.0.2/upack_3-4.0.2.pom" ];
    hash = "sha256-uf+67kBS2CsvzzSUbGO3qH0KZgQpqgvATYSdL2oXlz8=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upack_3/4.0.2";
  };

  "com.lihaoyi_upack_3-4.2.1" = fetchMaven {
    name = "com.lihaoyi_upack_3-4.2.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upack_3/4.2.1/upack_3-4.2.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upack_3/4.2.1/upack_3-4.2.1.pom" ];
    hash = "sha256-gk9n9biqodFspcrq/ICnMmDzhzR90gxoK1yRfqa9HRk=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upack_3/4.2.1";
  };

  "com.lihaoyi_upickle-core_3-4.0.2" = fetchMaven {
    name = "com.lihaoyi_upickle-core_3-4.0.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle-core_3/4.0.2/upickle-core_3-4.0.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle-core_3/4.0.2/upickle-core_3-4.0.2.pom" ];
    hash = "sha256-y+2kYNhenuu+ILt2x58+BXzpPEezMKi7hx8w+9s0a70=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle-core_3/4.0.2";
  };

  "com.lihaoyi_upickle-core_3-4.2.1" = fetchMaven {
    name = "com.lihaoyi_upickle-core_3-4.2.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle-core_3/4.2.1/upickle-core_3-4.2.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle-core_3/4.2.1/upickle-core_3-4.2.1.pom" ];
    hash = "sha256-ABYD12/Kjkj52Prk0+MJ0f3s5PlBsaqYiLcu/2fAzWY=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle-core_3/4.2.1";
  };

  "com.lihaoyi_upickle-implicits-named-tuples_3-4.2.1" = fetchMaven {
    name = "com.lihaoyi_upickle-implicits-named-tuples_3-4.2.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle-implicits-named-tuples_3/4.2.1/upickle-implicits-named-tuples_3-4.2.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle-implicits-named-tuples_3/4.2.1/upickle-implicits-named-tuples_3-4.2.1.pom" ];
    hash = "sha256-XxUXlAuCOtuoI4UDVDvrC718bsoL5HJgLUX1UoV3yUs=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle-implicits-named-tuples_3/4.2.1";
  };

  "com.lihaoyi_upickle-implicits_3-4.0.2" = fetchMaven {
    name = "com.lihaoyi_upickle-implicits_3-4.0.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle-implicits_3/4.0.2/upickle-implicits_3-4.0.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle-implicits_3/4.0.2/upickle-implicits_3-4.0.2.pom" ];
    hash = "sha256-spEOo3MUeUwRKHSk7Oc5n6RIseeDKhPKp/fe8NKQ1Mc=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle-implicits_3/4.0.2";
  };

  "com.lihaoyi_upickle-implicits_3-4.2.1" = fetchMaven {
    name = "com.lihaoyi_upickle-implicits_3-4.2.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle-implicits_3/4.2.1/upickle-implicits_3-4.2.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle-implicits_3/4.2.1/upickle-implicits_3-4.2.1.pom" ];
    hash = "sha256-Mg8F2NTFmm1VR6L6dcUtpFqnOjTGhvT8umCE67sCgiU=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle-implicits_3/4.2.1";
  };

  "com.lihaoyi_upickle_3-4.0.2" = fetchMaven {
    name = "com.lihaoyi_upickle_3-4.0.2";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle_3/4.0.2/upickle_3-4.0.2.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle_3/4.0.2/upickle_3-4.0.2.pom" ];
    hash = "sha256-9lijD0jcIIu+/InNWvfbdxF/DgmoB8ksVb7bl6BM1iU=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle_3/4.0.2";
  };

  "com.lihaoyi_upickle_3-4.2.1" = fetchMaven {
    name = "com.lihaoyi_upickle_3-4.2.1";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/upickle_3/4.2.1/upickle_3-4.2.1.jar" "https://repo1.maven.org/maven2/com/lihaoyi/upickle_3/4.2.1/upickle_3-4.2.1.pom" ];
    hash = "sha256-KjnsF2MI+zgkACRZHqHrn75XEa1Xy+Ip+fgUuCZyHqo=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/upickle_3/4.2.1";
  };

  "com.lihaoyi_utest_3-0.8.4" = fetchMaven {
    name = "com.lihaoyi_utest_3-0.8.4";
    urls = [ "https://repo1.maven.org/maven2/com/lihaoyi/utest_3/0.8.4/utest_3-0.8.4.jar" "https://repo1.maven.org/maven2/com/lihaoyi/utest_3/0.8.4/utest_3-0.8.4.pom" ];
    hash = "sha256-89ggPqD9zz3LlcKgfI6W4Zd0vrK1aQZ+UY8b4EZUAk4=";
    installPath = "https/repo1.maven.org/maven2/com/lihaoyi/utest_3/0.8.4";
  };

  "com.lmax_disruptor-3.4.2" = fetchMaven {
    name = "com.lmax_disruptor-3.4.2";
    urls = [ "https://repo1.maven.org/maven2/com/lmax/disruptor/3.4.2/disruptor-3.4.2.jar" "https://repo1.maven.org/maven2/com/lmax/disruptor/3.4.2/disruptor-3.4.2.pom" ];
    hash = "sha256-nbZsn6zL8HaJOrkMiWwvCuHQumcNQYA8e6QrAjXKKKg=";
    installPath = "https/repo1.maven.org/maven2/com/lmax/disruptor/3.4.2";
  };

  "com.lumidion_sonatype-central-client-core_3-0.5.0" = fetchMaven {
    name = "com.lumidion_sonatype-central-client-core_3-0.5.0";
    urls = [ "https://repo1.maven.org/maven2/com/lumidion/sonatype-central-client-core_3/0.5.0/sonatype-central-client-core_3-0.5.0.jar" "https://repo1.maven.org/maven2/com/lumidion/sonatype-central-client-core_3/0.5.0/sonatype-central-client-core_3-0.5.0.pom" ];
    hash = "sha256-3iqJJwp7ZjknrMjzYV7km5wsfKID/Aqfe4QUwtsGadU=";
    installPath = "https/repo1.maven.org/maven2/com/lumidion/sonatype-central-client-core_3/0.5.0";
  };

  "com.lumidion_sonatype-central-client-requests_3-0.5.0" = fetchMaven {
    name = "com.lumidion_sonatype-central-client-requests_3-0.5.0";
    urls = [ "https://repo1.maven.org/maven2/com/lumidion/sonatype-central-client-requests_3/0.5.0/sonatype-central-client-requests_3-0.5.0.jar" "https://repo1.maven.org/maven2/com/lumidion/sonatype-central-client-requests_3/0.5.0/sonatype-central-client-requests_3-0.5.0.pom" ];
    hash = "sha256-D04N9ZEVxyv/qRrgZ2ZOYyPyeiLPZHRgP2wkCog7kUs=";
    installPath = "https/repo1.maven.org/maven2/com/lumidion/sonatype-central-client-requests_3/0.5.0";
  };

  "com.lumidion_sonatype-central-client-upickle_3-0.5.0" = fetchMaven {
    name = "com.lumidion_sonatype-central-client-upickle_3-0.5.0";
    urls = [ "https://repo1.maven.org/maven2/com/lumidion/sonatype-central-client-upickle_3/0.5.0/sonatype-central-client-upickle_3-0.5.0.jar" "https://repo1.maven.org/maven2/com/lumidion/sonatype-central-client-upickle_3/0.5.0/sonatype-central-client-upickle_3-0.5.0.pom" ];
    hash = "sha256-Wrarn0UM2LjJJbLDgsZ6okwrZt6kvoZJJ/SGQNcZ/y0=";
    installPath = "https/repo1.maven.org/maven2/com/lumidion/sonatype-central-client-upickle_3/0.5.0";
  };

  "com.swoval_file-tree-views-2.1.12" = fetchMaven {
    name = "com.swoval_file-tree-views-2.1.12";
    urls = [ "https://repo1.maven.org/maven2/com/swoval/file-tree-views/2.1.12/file-tree-views-2.1.12.jar" "https://repo1.maven.org/maven2/com/swoval/file-tree-views/2.1.12/file-tree-views-2.1.12.pom" ];
    hash = "sha256-QhJJFQt5LS2THa8AyPLrj0suht4eCiAEl2sf7QsZU3I=";
    installPath = "https/repo1.maven.org/maven2/com/swoval/file-tree-views/2.1.12";
  };

  "guru.nidi_graphviz-java-0.18.1" = fetchMaven {
    name = "guru.nidi_graphviz-java-0.18.1";
    urls = [ "https://repo1.maven.org/maven2/guru/nidi/graphviz-java/0.18.1/graphviz-java-0.18.1.jar" "https://repo1.maven.org/maven2/guru/nidi/graphviz-java/0.18.1/graphviz-java-0.18.1.pom" ];
    hash = "sha256-Aq/u1Ss6/IoutsGna1uDSZ/+QNdDjfZmDZDh49OHNGs=";
    installPath = "https/repo1.maven.org/maven2/guru/nidi/graphviz-java/0.18.1";
  };

  "guru.nidi_graphviz-java-min-deps-0.18.1" = fetchMaven {
    name = "guru.nidi_graphviz-java-min-deps-0.18.1";
    urls = [ "https://repo1.maven.org/maven2/guru/nidi/graphviz-java-min-deps/0.18.1/graphviz-java-min-deps-0.18.1.jar" "https://repo1.maven.org/maven2/guru/nidi/graphviz-java-min-deps/0.18.1/graphviz-java-min-deps-0.18.1.pom" ];
    hash = "sha256-IJXiFPcJ1+FIHyUzXJWIWBecUp1qj2OcmQaHpUBpXKs=";
    installPath = "https/repo1.maven.org/maven2/guru/nidi/graphviz-java-min-deps/0.18.1";
  };

  "guru.nidi_graphviz-java-parent-0.18.1" = fetchMaven {
    name = "guru.nidi_graphviz-java-parent-0.18.1";
    urls = [ "https://repo1.maven.org/maven2/guru/nidi/graphviz-java-parent/0.18.1/graphviz-java-parent-0.18.1.pom" ];
    hash = "sha256-wjX7phg6GsC6AsCunFDeqktfCfHi0oW3WjsCNnBl8oQ=";
    installPath = "https/repo1.maven.org/maven2/guru/nidi/graphviz-java-parent/0.18.1";
  };

  "guru.nidi_guru-nidi-parent-pom-1.1.36" = fetchMaven {
    name = "guru.nidi_guru-nidi-parent-pom-1.1.36";
    urls = [ "https://repo1.maven.org/maven2/guru/nidi/guru-nidi-parent-pom/1.1.36/guru-nidi-parent-pom-1.1.36.pom" ];
    hash = "sha256-RywUAzcemtEHr3u6CYSTBA+NjVhrUilz8bM/EjOnBpE=";
    installPath = "https/repo1.maven.org/maven2/guru/nidi/guru-nidi-parent-pom/1.1.36";
  };

  "io.airlift_airbase-112" = fetchMaven {
    name = "io.airlift_airbase-112";
    urls = [ "https://repo1.maven.org/maven2/io/airlift/airbase/112/airbase-112.pom" ];
    hash = "sha256-I3jUuyAfPGbPcF0yDH+fa8l5rouZdvucoXg8tMLt174=";
    installPath = "https/repo1.maven.org/maven2/io/airlift/airbase/112";
  };

  "io.airlift_aircompressor-0.27" = fetchMaven {
    name = "io.airlift_aircompressor-0.27";
    urls = [ "https://repo1.maven.org/maven2/io/airlift/aircompressor/0.27/aircompressor-0.27.jar" "https://repo1.maven.org/maven2/io/airlift/aircompressor/0.27/aircompressor-0.27.pom" ];
    hash = "sha256-mxNNsdJ5O/jd2kv4pEyG7kFfnxLqrYDMPtxys0c1wuM=";
    installPath = "https/repo1.maven.org/maven2/io/airlift/aircompressor/0.27";
  };

  "io.get-coursier_cache-util-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_cache-util-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/cache-util/2.1.25-M13/cache-util-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/cache-util/2.1.25-M13/cache-util-2.1.25-M13.pom" ];
    hash = "sha256-dgdCjsp+Et/FHpfmwIfxEdsgoacfC3V2wJfDZAWkcH8=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/cache-util/2.1.25-M13";
  };

  "io.get-coursier_coursier-cache_2.13-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-cache_2.13-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-cache_2.13/2.1.25-M13/coursier-cache_2.13-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-cache_2.13/2.1.25-M13/coursier-cache_2.13-2.1.25-M13.pom" ];
    hash = "sha256-pxG4F5eTvhrSpXxi1QhsTe3fbG32QyR0WvWMWhm8fZM=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-cache_2.13/2.1.25-M13";
  };

  "io.get-coursier_coursier-core_2.13-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-core_2.13-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-core_2.13/2.1.25-M13/coursier-core_2.13-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-core_2.13/2.1.25-M13/coursier-core_2.13-2.1.25-M13.pom" ];
    hash = "sha256-oEmW8ssv4y5eXRfi0fhzrO2cbKkR589D63WkfrMxFcg=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-core_2.13/2.1.25-M13";
  };

  "io.get-coursier_coursier-env_2.13-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-env_2.13-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-env_2.13/2.1.25-M13/coursier-env_2.13-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-env_2.13/2.1.25-M13/coursier-env_2.13-2.1.25-M13.pom" ];
    hash = "sha256-89tge25PHOgMK1NkHKCmwyvSs/ubZKgxy2IXhTnHg1k=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-env_2.13/2.1.25-M13";
  };

  "io.get-coursier_coursier-exec-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-exec-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-exec/2.1.25-M13/coursier-exec-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-exec/2.1.25-M13/coursier-exec-2.1.25-M13.pom" ];
    hash = "sha256-6SObePXadtlIOydr35uonwF7wj024vWFkwDsJH5XKEw=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-exec/2.1.25-M13";
  };

  "io.get-coursier_coursier-jvm_2.13-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-jvm_2.13-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-jvm_2.13/2.1.25-M13/coursier-jvm_2.13-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-jvm_2.13/2.1.25-M13/coursier-jvm_2.13-2.1.25-M13.pom" ];
    hash = "sha256-+x2cTk7xsDyfoRl2Kqt3F01wTfJX5GqF/up1rxclXzQ=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-jvm_2.13/2.1.25-M13";
  };

  "io.get-coursier_coursier-proxy-setup-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-proxy-setup-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-proxy-setup/2.1.25-M13/coursier-proxy-setup-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-proxy-setup/2.1.25-M13/coursier-proxy-setup-2.1.25-M13.pom" ];
    hash = "sha256-2+iF8LROBOmkmWUde0dHr34fBGHwVrpVLsPiDmth+VQ=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-proxy-setup/2.1.25-M13";
  };

  "io.get-coursier_coursier-util_2.13-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier-util_2.13-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier-util_2.13/2.1.25-M13/coursier-util_2.13-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier-util_2.13/2.1.25-M13/coursier-util_2.13-2.1.25-M13.pom" ];
    hash = "sha256-YUuYAcCcAruQaozNipGROL0Cp0jpAsXfLiMum33x4eU=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier-util_2.13/2.1.25-M13";
  };

  "io.get-coursier_coursier_2.13-2.1.25-M13" = fetchMaven {
    name = "io.get-coursier_coursier_2.13-2.1.25-M13";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/coursier_2.13/2.1.25-M13/coursier_2.13-2.1.25-M13.jar" "https://repo1.maven.org/maven2/io/get-coursier/coursier_2.13/2.1.25-M13/coursier_2.13-2.1.25-M13.pom" ];
    hash = "sha256-W3hJkfr8eHtU6N2PGXvfEmjT8VtWgogL62SQMitpnNg=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/coursier_2.13/2.1.25-M13";
  };

  "io.get-coursier_dependency_2.13-0.3.2" = fetchMaven {
    name = "io.get-coursier_dependency_2.13-0.3.2";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/dependency_2.13/0.3.2/dependency_2.13-0.3.2.jar" "https://repo1.maven.org/maven2/io/get-coursier/dependency_2.13/0.3.2/dependency_2.13-0.3.2.pom" ];
    hash = "sha256-kLCTLMEFNrY74GFqcr7Vw/qEbR7CPpskXrpzbbH0gMg=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/dependency_2.13/0.3.2";
  };

  "io.get-coursier_versions_2.13-0.5.1" = fetchMaven {
    name = "io.get-coursier_versions_2.13-0.5.1";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/versions_2.13/0.5.1/versions_2.13-0.5.1.jar" "https://repo1.maven.org/maven2/io/get-coursier/versions_2.13/0.5.1/versions_2.13-0.5.1.pom" ];
    hash = "sha256-1ryxcGeeUu18sLY4gL2cDVfOkh59oRPmNnIA0N2G1/Y=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/versions_2.13/0.5.1";
  };

  "io.netty_netty-bom-4.1.117.Final" = fetchMaven {
    name = "io.netty_netty-bom-4.1.117.Final";
    urls = [ "https://repo1.maven.org/maven2/io/netty/netty-bom/4.1.117.Final/netty-bom-4.1.117.Final.pom" ];
    hash = "sha256-Ej4z3zNHEg2xiuYyNcdq+UJT7XC01ITGAlWCyc5V6cU=";
    installPath = "https/repo1.maven.org/maven2/io/netty/netty-bom/4.1.117.Final";
  };

  "jakarta.platform_jakarta.jakartaee-bom-9.1.0" = fetchMaven {
    name = "jakarta.platform_jakarta.jakartaee-bom-9.1.0";
    urls = [ "https://repo1.maven.org/maven2/jakarta/platform/jakarta.jakartaee-bom/9.1.0/jakarta.jakartaee-bom-9.1.0.pom" ];
    hash = "sha256-kstGe15Yw9oF6LQ3Vovx1PcCUfQtNaEM7T8E5Upp1gg=";
    installPath = "https/repo1.maven.org/maven2/jakarta/platform/jakarta.jakartaee-bom/9.1.0";
  };

  "jakarta.platform_jakartaee-api-parent-9.1.0" = fetchMaven {
    name = "jakarta.platform_jakartaee-api-parent-9.1.0";
    urls = [ "https://repo1.maven.org/maven2/jakarta/platform/jakartaee-api-parent/9.1.0/jakartaee-api-parent-9.1.0.pom" ];
    hash = "sha256-FrD7N30UkkRSQtD3+FPOC1fH2qrNnJw6UZQ/hNFXWrA=";
    installPath = "https/repo1.maven.org/maven2/jakarta/platform/jakartaee-api-parent/9.1.0";
  };

  "javax.inject_javax.inject-1" = fetchMaven {
    name = "javax.inject_javax.inject-1";
    urls = [ "https://repo1.maven.org/maven2/javax/inject/javax.inject/1/javax.inject-1.jar" "https://repo1.maven.org/maven2/javax/inject/javax.inject/1/javax.inject-1.pom" ];
    hash = "sha256-CZm6Lb7D5az8nprqBvjNerGQjB0xPaY56/RvKwSZIxE=";
    installPath = "https/repo1.maven.org/maven2/javax/inject/javax.inject/1";
  };

  "net.openhft_java-parent-pom-1.1.28" = fetchMaven {
    name = "net.openhft_java-parent-pom-1.1.28";
    urls = [ "https://repo1.maven.org/maven2/net/openhft/java-parent-pom/1.1.28/java-parent-pom-1.1.28.pom" ];
    hash = "sha256-d7bOKP/hHJElmDQtIbblYDHRc8LCpqkt5Zl8aHp7l88=";
    installPath = "https/repo1.maven.org/maven2/net/openhft/java-parent-pom/1.1.28";
  };

  "net.openhft_root-parent-pom-1.2.12" = fetchMaven {
    name = "net.openhft_root-parent-pom-1.2.12";
    urls = [ "https://repo1.maven.org/maven2/net/openhft/root-parent-pom/1.2.12/root-parent-pom-1.2.12.pom" ];
    hash = "sha256-D/M1qN+njmMZWqS5h27fl83Q+zWgIFjaYQkCpD2Oy/M=";
    installPath = "https/repo1.maven.org/maven2/net/openhft/root-parent-pom/1.2.12";
  };

  "net.openhft_zero-allocation-hashing-0.16" = fetchMaven {
    name = "net.openhft_zero-allocation-hashing-0.16";
    urls = [ "https://repo1.maven.org/maven2/net/openhft/zero-allocation-hashing/0.16/zero-allocation-hashing-0.16.jar" "https://repo1.maven.org/maven2/net/openhft/zero-allocation-hashing/0.16/zero-allocation-hashing-0.16.pom" ];
    hash = "sha256-QkNOGkyP/OFWM+pv40hqR+ii4GBAcv0bbIrpG66YDMo=";
    installPath = "https/repo1.maven.org/maven2/net/openhft/zero-allocation-hashing/0.16";
  };

  "nl.big-o_liqp-0.8.2" = fetchMaven {
    name = "nl.big-o_liqp-0.8.2";
    urls = [ "https://repo1.maven.org/maven2/nl/big-o/liqp/0.8.2/liqp-0.8.2.jar" "https://repo1.maven.org/maven2/nl/big-o/liqp/0.8.2/liqp-0.8.2.pom" ];
    hash = "sha256-yamgRk2t6//LGTLwLSNJ28rGL0mQFOU1XCThtpWwmMM=";
    installPath = "https/repo1.maven.org/maven2/nl/big-o/liqp/0.8.2";
  };

  "org.antlr_antlr4-master-4.7.2" = fetchMaven {
    name = "org.antlr_antlr4-master-4.7.2";
    urls = [ "https://repo1.maven.org/maven2/org/antlr/antlr4-master/4.7.2/antlr4-master-4.7.2.pom" ];
    hash = "sha256-Z+4f52KXe+J8mvu6l3IryRrYdsxjwj4Cztrn0OEs2dM=";
    installPath = "https/repo1.maven.org/maven2/org/antlr/antlr4-master/4.7.2";
  };

  "org.antlr_antlr4-runtime-4.7.2" = fetchMaven {
    name = "org.antlr_antlr4-runtime-4.7.2";
    urls = [ "https://repo1.maven.org/maven2/org/antlr/antlr4-runtime/4.7.2/antlr4-runtime-4.7.2.jar" "https://repo1.maven.org/maven2/org/antlr/antlr4-runtime/4.7.2/antlr4-runtime-4.7.2.pom" ];
    hash = "sha256-orSo+dX/By8iQ7guGqi/mScUKmFeAp2TizPRFWLVUvY=";
    installPath = "https/repo1.maven.org/maven2/org/antlr/antlr4-runtime/4.7.2";
  };

  "org.apache_apache-13" = fetchMaven {
    name = "org.apache_apache-13";
    urls = [ "https://repo1.maven.org/maven2/org/apache/apache/13/apache-13.pom" ];
    hash = "sha256-sACBC2XyW8OQOMbX09EPCVL/lqUvROHaHHHiQ3XpTk4=";
    installPath = "https/repo1.maven.org/maven2/org/apache/apache/13";
  };

  "org.apache_apache-30" = fetchMaven {
    name = "org.apache_apache-30";
    urls = [ "https://repo1.maven.org/maven2/org/apache/apache/30/apache-30.pom" ];
    hash = "sha256-Wo5syVryUH2A6IG2gydSxmAb8DYNxV6MmKxGHd1FxcE=";
    installPath = "https/repo1.maven.org/maven2/org/apache/apache/30";
  };

  "org.apache_apache-31" = fetchMaven {
    name = "org.apache_apache-31";
    urls = [ "https://repo1.maven.org/maven2/org/apache/apache/31/apache-31.pom" ];
    hash = "sha256-Evktp+xRZ2C/VvG0UDTcFRSEvvSJINCtIe0Rom2159s=";
    installPath = "https/repo1.maven.org/maven2/org/apache/apache/31";
  };

  "org.apache_apache-33" = fetchMaven {
    name = "org.apache_apache-33";
    urls = [ "https://repo1.maven.org/maven2/org/apache/apache/33/apache-33.pom" ];
    hash = "sha256-Hwj0S/ETiRxq9ObIzy9OGjGShFgbWuJOEoV6skSMQzI=";
    installPath = "https/repo1.maven.org/maven2/org/apache/apache/33";
  };

  "org.apache_apache-6" = fetchMaven {
    name = "org.apache_apache-6";
    urls = [ "https://repo1.maven.org/maven2/org/apache/apache/6/apache-6.pom" ];
    hash = "sha256-A7aDRlGjS4P3/QlZmvMRdVHhP4yqTFL4wZbRnp1lJ9U=";
    installPath = "https/repo1.maven.org/maven2/org/apache/apache/6";
  };

  "org.checkerframework_checker-qual-3.5.0" = fetchMaven {
    name = "org.checkerframework_checker-qual-3.5.0";
    urls = [ "https://repo1.maven.org/maven2/org/checkerframework/checker-qual/3.5.0/checker-qual-3.5.0.jar" "https://repo1.maven.org/maven2/org/checkerframework/checker-qual/3.5.0/checker-qual-3.5.0.pom" ];
    hash = "sha256-7lxlpTC52iRt4ZSq/jCM3ohl9uRC4V8WTpNF+DLWZrU=";
    installPath = "https/repo1.maven.org/maven2/org/checkerframework/checker-qual/3.5.0";
  };

  "org.fusesource_fusesource-pom-1.12" = fetchMaven {
    name = "org.fusesource_fusesource-pom-1.12";
    urls = [ "https://repo1.maven.org/maven2/org/fusesource/fusesource-pom/1.12/fusesource-pom-1.12.pom" ];
    hash = "sha256-NUD5PZ1FYYOq8yumvT5i29Vxd2ZCI6PXImXfLe4mE30=";
    installPath = "https/repo1.maven.org/maven2/org/fusesource/fusesource-pom/1.12";
  };

  "org.jetbrains_annotations-15.0" = fetchMaven {
    name = "org.jetbrains_annotations-15.0";
    urls = [ "https://repo1.maven.org/maven2/org/jetbrains/annotations/15.0/annotations-15.0.jar" "https://repo1.maven.org/maven2/org/jetbrains/annotations/15.0/annotations-15.0.pom" ];
    hash = "sha256-zKx9CDgM9iLkt5SFNiSgDzJu9AxFNPjCFWwMi9copnI=";
    installPath = "https/repo1.maven.org/maven2/org/jetbrains/annotations/15.0";
  };

  "org.jgrapht_jgrapht-1.4.0" = fetchMaven {
    name = "org.jgrapht_jgrapht-1.4.0";
    urls = [ "https://repo1.maven.org/maven2/org/jgrapht/jgrapht/1.4.0/jgrapht-1.4.0.pom" ];
    hash = "sha256-0bLt1jNIcVaLnLF7J/UT53p9nsmR1nSB3zKHCCc9xY0=";
    installPath = "https/repo1.maven.org/maven2/org/jgrapht/jgrapht/1.4.0";
  };

  "org.jgrapht_jgrapht-core-1.4.0" = fetchMaven {
    name = "org.jgrapht_jgrapht-core-1.4.0";
    urls = [ "https://repo1.maven.org/maven2/org/jgrapht/jgrapht-core/1.4.0/jgrapht-core-1.4.0.jar" "https://repo1.maven.org/maven2/org/jgrapht/jgrapht-core/1.4.0/jgrapht-core-1.4.0.pom" ];
    hash = "sha256-SDTdRtbcTa+IsuGfLrnZjaDdEkUaxolSHKwTM1uyKII=";
    installPath = "https/repo1.maven.org/maven2/org/jgrapht/jgrapht-core/1.4.0";
  };

  "org.jheaps_jheaps-0.11" = fetchMaven {
    name = "org.jheaps_jheaps-0.11";
    urls = [ "https://repo1.maven.org/maven2/org/jheaps/jheaps/0.11/jheaps-0.11.jar" "https://repo1.maven.org/maven2/org/jheaps/jheaps/0.11/jheaps-0.11.pom" ];
    hash = "sha256-LtDxiqSoClaeIxb0UUbh79Y8HiSHrgyVLCMhQSjRDUo=";
    installPath = "https/repo1.maven.org/maven2/org/jheaps/jheaps/0.11";
  };

  "org.jline_jline-3.28.0" = fetchMaven {
    name = "org.jline_jline-3.28.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline/3.28.0/jline-3.28.0.jar" "https://repo1.maven.org/maven2/org/jline/jline/3.28.0/jline-3.28.0.pom" ];
    hash = "sha256-wZ5jyl7lsoQtyWbLMxzbcbpHf7HqdKEuIqGlgU8n58w=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline/3.28.0";
  };

  "org.jline_jline-native-3.27.0" = fetchMaven {
    name = "org.jline_jline-native-3.27.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-native/3.27.0/jline-native-3.27.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-native/3.27.0/jline-native-3.27.0.pom" ];
    hash = "sha256-O/J+a5uNpfdl2iYqzl0POxqp0CtLNjdWJw9LaxV82GY=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-native/3.27.0";
  };

  "org.jline_jline-native-3.29.0" = fetchMaven {
    name = "org.jline_jline-native-3.29.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-native/3.29.0/jline-native-3.29.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-native/3.29.0/jline-native-3.29.0.pom" ];
    hash = "sha256-B4uPEOoZQdIyvNzjJBxzr+9m6E0Q95p2l/0iyYpz62Y=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-native/3.29.0";
  };

  "org.jline_jline-parent-3.27.0" = fetchMaven {
    name = "org.jline_jline-parent-3.27.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-parent/3.27.0/jline-parent-3.27.0.pom" ];
    hash = "sha256-Oh7mRotS8yhoU5Nxigu+kfgUDILIgwtkQXCkvE1JesQ=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-parent/3.27.0";
  };

  "org.jline_jline-parent-3.27.1" = fetchMaven {
    name = "org.jline_jline-parent-3.27.1";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-parent/3.27.1/jline-parent-3.27.1.pom" ];
    hash = "sha256-Oa5DgBvf5JwZH68PDIyNkEQtm7IL04ujoeniH6GZas8=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-parent/3.27.1";
  };

  "org.jline_jline-parent-3.28.0" = fetchMaven {
    name = "org.jline_jline-parent-3.28.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-parent/3.28.0/jline-parent-3.28.0.pom" ];
    hash = "sha256-EvTBMv2vy2Fr4PBgLlyFTBOBTND+rNcodOzplY4Rq/g=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-parent/3.28.0";
  };

  "org.jline_jline-parent-3.29.0" = fetchMaven {
    name = "org.jline_jline-parent-3.29.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-parent/3.29.0/jline-parent-3.29.0.pom" ];
    hash = "sha256-oxKMIwjIJO0c7pcRwCh1deR9MT5oIjEQD5xiDZzCLNg=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-parent/3.29.0";
  };

  "org.jline_jline-reader-3.27.0" = fetchMaven {
    name = "org.jline_jline-reader-3.27.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-reader/3.27.0/jline-reader-3.27.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-reader/3.27.0/jline-reader-3.27.0.pom" ];
    hash = "sha256-f/b+aWF/tmHedVWseL7hDjA4vJUrllPGnNhZH81S3Qg=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-reader/3.27.0";
  };

  "org.jline_jline-reader-3.29.0" = fetchMaven {
    name = "org.jline_jline-reader-3.29.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-reader/3.29.0/jline-reader-3.29.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-reader/3.29.0/jline-reader-3.29.0.pom" ];
    hash = "sha256-29VGA1VapJEewqh+CohsyXSpXkH7It/GwcAK0Z4igbo=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-reader/3.29.0";
  };

  "org.jline_jline-terminal-3.27.0" = fetchMaven {
    name = "org.jline_jline-terminal-3.27.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-terminal/3.27.0/jline-terminal-3.27.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-terminal/3.27.0/jline-terminal-3.27.0.pom" ];
    hash = "sha256-hkKgeb/Kl1hlTC9TMNkujoBwY+QS4e6ESUK9kdEbcGE=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-terminal/3.27.0";
  };

  "org.jline_jline-terminal-3.27.1" = fetchMaven {
    name = "org.jline_jline-terminal-3.27.1";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-terminal/3.27.1/jline-terminal-3.27.1.jar" "https://repo1.maven.org/maven2/org/jline/jline-terminal/3.27.1/jline-terminal-3.27.1.pom" ];
    hash = "sha256-WV77BAEncauTljUBrlYi9v3GxDDeskqQpHHD9Fdbqjw=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-terminal/3.27.1";
  };

  "org.jline_jline-terminal-3.29.0" = fetchMaven {
    name = "org.jline_jline-terminal-3.29.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-terminal/3.29.0/jline-terminal-3.29.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-terminal/3.29.0/jline-terminal-3.29.0.pom" ];
    hash = "sha256-VSLgLannbVTHJdbWjmHtvPlbqRHgN67iVGQhd6GdBrI=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-terminal/3.29.0";
  };

  "org.jline_jline-terminal-jna-3.27.0" = fetchMaven {
    name = "org.jline_jline-terminal-jna-3.27.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-terminal-jna/3.27.0/jline-terminal-jna-3.27.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-terminal-jna/3.27.0/jline-terminal-jna-3.27.0.pom" ];
    hash = "sha256-Pw8jJMTTBpAKxfU9gp2EN2CfVHpRpC0YJorCu/9UDsI=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-terminal-jna/3.27.0";
  };

  "org.jline_jline-terminal-jni-3.27.1" = fetchMaven {
    name = "org.jline_jline-terminal-jni-3.27.1";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-terminal-jni/3.27.1/jline-terminal-jni-3.27.1.jar" "https://repo1.maven.org/maven2/org/jline/jline-terminal-jni/3.27.1/jline-terminal-jni-3.27.1.pom" ];
    hash = "sha256-AWKC7imb/rnF39PAo3bVIW430zPkyj9WozKGkPlTTBE=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-terminal-jni/3.27.1";
  };

  "org.jline_jline-terminal-jni-3.29.0" = fetchMaven {
    name = "org.jline_jline-terminal-jni-3.29.0";
    urls = [ "https://repo1.maven.org/maven2/org/jline/jline-terminal-jni/3.29.0/jline-terminal-jni-3.29.0.jar" "https://repo1.maven.org/maven2/org/jline/jline-terminal-jni/3.29.0/jline-terminal-jni-3.29.0.pom" ];
    hash = "sha256-P5vIZblvy8nL21syHeJMNJEip/JVsVkislqKbh6ffyA=";
    installPath = "https/repo1.maven.org/maven2/org/jline/jline-terminal-jni/3.29.0";
  };

  "org.jsoup_jsoup-1.17.2" = fetchMaven {
    name = "org.jsoup_jsoup-1.17.2";
    urls = [ "https://repo1.maven.org/maven2/org/jsoup/jsoup/1.17.2/jsoup-1.17.2.jar" "https://repo1.maven.org/maven2/org/jsoup/jsoup/1.17.2/jsoup-1.17.2.pom" ];
    hash = "sha256-aex/2xWBJBV0CVGOIoNvOcnYi6sVTd3CwBJhM5ZUISU=";
    installPath = "https/repo1.maven.org/maven2/org/jsoup/jsoup/1.17.2";
  };

  "org.junit_junit-bom-5.10.0" = fetchMaven {
    name = "org.junit_junit-bom-5.10.0";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.10.0/junit-bom-5.10.0.pom" ];
    hash = "sha256-luQjQgOITEqh2Y+/2XwfXzgggI8aRglNmIXZGpcJEgY=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.10.0";
  };

  "org.junit_junit-bom-5.10.2" = fetchMaven {
    name = "org.junit_junit-bom-5.10.2";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.10.2/junit-bom-5.10.2.pom" ];
    hash = "sha256-AlDFqi7NIm0J1UoA6JCUM3Rhq5cNwsXq/I8viZmWLEg=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.10.2";
  };

  "org.junit_junit-bom-5.10.3" = fetchMaven {
    name = "org.junit_junit-bom-5.10.3";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.10.3/junit-bom-5.10.3.pom" ];
    hash = "sha256-V+Pp8ndKoaD1fkc4oK9oU0+rrJ5hFRyuVcUnD0LI2Fw=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.10.3";
  };

  "org.junit_junit-bom-5.11.2" = fetchMaven {
    name = "org.junit_junit-bom-5.11.2";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.11.2/junit-bom-5.11.2.pom" ];
    hash = "sha256-cGHayaCE9Q75/hyJE3iFhnmKFYtzLY/MLSHDid0QSHY=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.11.2";
  };

  "org.junit_junit-bom-5.11.4" = fetchMaven {
    name = "org.junit_junit-bom-5.11.4";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.11.4/junit-bom-5.11.4.pom" ];
    hash = "sha256-nbbdpbMILETuwuXYxim5wKdWe4U5JhdP8wechYIZuZQ=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.11.4";
  };

  "org.junit_junit-bom-5.8.0-M1" = fetchMaven {
    name = "org.junit_junit-bom-5.8.0-M1";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.8.0-M1/junit-bom-5.8.0-M1.pom" ];
    hash = "sha256-3suC6i7s+f+GrkY/p8I8TXqZnkP6Vz5/iHplYFZPIk4=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.8.0-M1";
  };

  "org.junit_junit-bom-5.9.2" = fetchMaven {
    name = "org.junit_junit-bom-5.9.2";
    urls = [ "https://repo1.maven.org/maven2/org/junit/junit-bom/5.9.2/junit-bom-5.9.2.pom" ];
    hash = "sha256-uGn68+1/ScKIRXjMgUllMofOsjFTxO1mfwrpSVBpP6E=";
    installPath = "https/repo1.maven.org/maven2/org/junit/junit-bom/5.9.2";
  };

  "org.mockito_mockito-bom-4.11.0" = fetchMaven {
    name = "org.mockito_mockito-bom-4.11.0";
    urls = [ "https://repo1.maven.org/maven2/org/mockito/mockito-bom/4.11.0/mockito-bom-4.11.0.pom" ];
    hash = "sha256-jtuaGRrHXNkevtfBAzk3OA+n5RNtrDQ0MQSqSRxUIfc=";
    installPath = "https/repo1.maven.org/maven2/org/mockito/mockito-bom/4.11.0";
  };

  "org.ow2_ow2-1.5.1" = fetchMaven {
    name = "org.ow2_ow2-1.5.1";
    urls = [ "https://repo1.maven.org/maven2/org/ow2/ow2/1.5.1/ow2-1.5.1.pom" ];
    hash = "sha256-4F8xYVbQg2PG/GhDEdcvENureaBF1yT/hSdLimkz5ks=";
    installPath = "https/repo1.maven.org/maven2/org/ow2/ow2/1.5.1";
  };

  "org.scala-lang_scala-compiler-2.13.13" = fetchMaven {
    name = "org.scala-lang_scala-compiler-2.13.13";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala-compiler/2.13.13/scala-compiler-2.13.13.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala-compiler/2.13.13/scala-compiler-2.13.13.pom" ];
    hash = "sha256-lHIX4OLYQ6PsAVqjFMEzct6Z/lCeUtfLw1OhFAUoMd8=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala-compiler/2.13.13";
  };

  "org.scala-lang_scala-compiler-2.13.15" = fetchMaven {
    name = "org.scala-lang_scala-compiler-2.13.15";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala-compiler/2.13.15/scala-compiler-2.13.15.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala-compiler/2.13.15/scala-compiler-2.13.15.pom" ];
    hash = "sha256-kvqWoFLNy3LGIbD6l67f66OyJq/K2L4rTStLiDzIzm8=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala-compiler/2.13.15";
  };

  "org.scala-lang_scala-library-2.13.15" = fetchMaven {
    name = "org.scala-lang_scala-library-2.13.15";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.15/scala-library-2.13.15.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.15/scala-library-2.13.15.pom" ];
    hash = "sha256-JnbDGZQKZZswRZuxauQywH/4rXzwzn++kMB4lw3OfPI=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.15";
  };

  "org.scala-lang_scala-library-2.13.16" = fetchMaven {
    name = "org.scala-lang_scala-library-2.13.16";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.16/scala-library-2.13.16.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.16/scala-library-2.13.16.pom" ];
    hash = "sha256-7/NvAxKKPtghJ/+pTNxvmIAiAdtQXRTUvDwGGXwpnpU=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.16";
  };

  "org.scala-lang_scala-reflect-2.13.15" = fetchMaven {
    name = "org.scala-lang_scala-reflect-2.13.15";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala-reflect/2.13.15/scala-reflect-2.13.15.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala-reflect/2.13.15/scala-reflect-2.13.15.pom" ];
    hash = "sha256-zmUU4hTEf5HC311UaNIHmzjSwWSbjXn6DyPP7ZzFy/8=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala-reflect/2.13.15";
  };

  "org.scala-lang_scala3-compiler_3-3.6.2" = fetchMaven {
    name = "org.scala-lang_scala3-compiler_3-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-compiler_3/3.6.2/scala3-compiler_3-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-compiler_3/3.6.2/scala3-compiler_3-3.6.2.pom" ];
    hash = "sha256-4wUykwZ0qw8x1WH5xNJwCP52I7326oM2XtWjeoDir+Y=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-compiler_3/3.6.2";
  };

  "org.scala-lang_scala3-compiler_3-3.7.1" = fetchMaven {
    name = "org.scala-lang_scala3-compiler_3-3.7.1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-compiler_3/3.7.1/scala3-compiler_3-3.7.1.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-compiler_3/3.7.1/scala3-compiler_3-3.7.1.pom" ];
    hash = "sha256-GBnDisJqCZ02jGKF0JwXpNaI0q0Q62GmcEHKDUlgKg4=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-compiler_3/3.7.1";
  };

  "org.scala-lang_scala3-interfaces-3.6.2" = fetchMaven {
    name = "org.scala-lang_scala3-interfaces-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-interfaces/3.6.2/scala3-interfaces-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-interfaces/3.6.2/scala3-interfaces-3.6.2.pom" ];
    hash = "sha256-MQJryHiMDS2t2CsumeP0ciN9Q9ehju7Fh7jBpq4c+D0=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-interfaces/3.6.2";
  };

  "org.scala-lang_scala3-interfaces-3.7.1" = fetchMaven {
    name = "org.scala-lang_scala3-interfaces-3.7.1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-interfaces/3.7.1/scala3-interfaces-3.7.1.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-interfaces/3.7.1/scala3-interfaces-3.7.1.pom" ];
    hash = "sha256-uX6I4vMRf8FU2hYYOEfk4+9urArnOhxpHIyDr5Uvdig=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-interfaces/3.7.1";
  };

  "org.scala-lang_scala3-library_3-3.6.2" = fetchMaven {
    name = "org.scala-lang_scala3-library_3-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.6.2/scala3-library_3-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.6.2/scala3-library_3-3.6.2.pom" ];
    hash = "sha256-eBeOgZMRztMgvVXj9zFkXwPRxDgmkiBSxMtzoFxUOiU=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.6.2";
  };

  "org.scala-lang_scala3-library_3-3.7.1" = fetchMaven {
    name = "org.scala-lang_scala3-library_3-3.7.1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.7.1/scala3-library_3-3.7.1.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.7.1/scala3-library_3-3.7.1.pom" ];
    hash = "sha256-MXZ0rOL5zzaa0E13ycpq1OEK5Po+YkvPy72gZ9tljAw=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.7.1";
  };

  "org.scala-lang_scala3-sbt-bridge-3.6.2" = fetchMaven {
    name = "org.scala-lang_scala3-sbt-bridge-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-sbt-bridge/3.6.2/scala3-sbt-bridge-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-sbt-bridge/3.6.2/scala3-sbt-bridge-3.6.2.pom" ];
    hash = "sha256-ouyRb3uSwsyJZkQkVqfY0ECascZSRBkzCSpi5F1GQG0=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-sbt-bridge/3.6.2";
  };

  "org.scala-lang_scala3-sbt-bridge-3.7.1" = fetchMaven {
    name = "org.scala-lang_scala3-sbt-bridge-3.7.1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-sbt-bridge/3.7.1/scala3-sbt-bridge-3.7.1.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-sbt-bridge/3.7.1/scala3-sbt-bridge-3.7.1.pom" ];
    hash = "sha256-8XbMq6BVzf3LwwXUIcpZMACKRNiYOuccfyFeyCY9iNk=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-sbt-bridge/3.7.1";
  };

  "org.scala-lang_scala3-tasty-inspector_3-3.6.2" = fetchMaven {
    name = "org.scala-lang_scala3-tasty-inspector_3-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scala3-tasty-inspector_3/3.6.2/scala3-tasty-inspector_3-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/scala3-tasty-inspector_3/3.6.2/scala3-tasty-inspector_3-3.6.2.pom" ];
    hash = "sha256-PxXdYKIHwHoMfldTzPq7PqtQF+1YzPqh0Ma2ue70yxE=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scala3-tasty-inspector_3/3.6.2";
  };

  "org.scala-lang_scaladoc_3-3.6.2" = fetchMaven {
    name = "org.scala-lang_scaladoc_3-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scaladoc_3/3.6.2/scaladoc_3-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/scaladoc_3/3.6.2/scaladoc_3-3.6.2.pom" ];
    hash = "sha256-BxzI0JCs9p8INscqFDoOV9HJIB+YM7EI0mCel7KoeBU=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scaladoc_3/3.6.2";
  };

  "org.scala-lang_scalap-2.13.13" = fetchMaven {
    name = "org.scala-lang_scalap-2.13.13";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/scalap/2.13.13/scalap-2.13.13.jar" "https://repo1.maven.org/maven2/org/scala-lang/scalap/2.13.13/scalap-2.13.13.pom" ];
    hash = "sha256-FQU2K0U7XRRmSS7/rFeyQ/QbbPabsJ45Jy5LxhP6IoM=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/scalap/2.13.13";
  };

  "org.scala-lang_tasty-core_3-3.6.2" = fetchMaven {
    name = "org.scala-lang_tasty-core_3-3.6.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/tasty-core_3/3.6.2/tasty-core_3-3.6.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/tasty-core_3/3.6.2/tasty-core_3-3.6.2.pom" ];
    hash = "sha256-StXvfqkjPpP18knWBc0UZv0bqzViP2FxFGMc5A1wQxw=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/tasty-core_3/3.6.2";
  };

  "org.scala-lang_tasty-core_3-3.7.1" = fetchMaven {
    name = "org.scala-lang_tasty-core_3-3.7.1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/tasty-core_3/3.7.1/tasty-core_3-3.7.1.jar" "https://repo1.maven.org/maven2/org/scala-lang/tasty-core_3/3.7.1/tasty-core_3-3.7.1.pom" ];
    hash = "sha256-Aj6sDzCKOvAYSE0N0ofh5u399m7qUaKwDIjo60jpFzc=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/tasty-core_3/3.7.1";
  };

  "org.scala-sbt_collections_2.13-1.10.7" = fetchMaven {
    name = "org.scala-sbt_collections_2.13-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/collections_2.13/1.10.7/collections_2.13-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/collections_2.13/1.10.7/collections_2.13-1.10.7.pom" ];
    hash = "sha256-y4FuwehuxB+70YBIKj5jH9L8tQpHrWFpPc9VrBUzM6Y=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/collections_2.13/1.10.7";
  };

  "org.scala-sbt_compiler-bridge_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_compiler-bridge_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/compiler-bridge_2.13/1.10.8/compiler-bridge_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/compiler-bridge_2.13/1.10.8/compiler-bridge_2.13-1.10.8.pom" ];
    hash = "sha256-qUQM76N3eZZj+d0Xdc/tB9TZwBaqLLSU10zu9LOKzqE=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/compiler-bridge_2.13/1.10.8";
  };

  "org.scala-sbt_compiler-interface-1.10.7" = fetchMaven {
    name = "org.scala-sbt_compiler-interface-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.10.7/compiler-interface-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.10.7/compiler-interface-1.10.7.pom" ];
    hash = "sha256-nFVs4vEVTEPSiGce3C77TTjvffSU+SMrn9KgV9xGVP0=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.10.7";
  };

  "org.scala-sbt_compiler-interface-1.10.8" = fetchMaven {
    name = "org.scala-sbt_compiler-interface-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.10.8/compiler-interface-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.10.8/compiler-interface-1.10.8.pom" ];
    hash = "sha256-3ajeQYhoP+Vqe05uXnwbwA5KAgIeLizUM6rorISKVMU=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.10.8";
  };

  "org.scala-sbt_compiler-interface-1.9.6" = fetchMaven {
    name = "org.scala-sbt_compiler-interface-1.9.6";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.9.6/compiler-interface-1.9.6.jar" "https://repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.9.6/compiler-interface-1.9.6.pom" ];
    hash = "sha256-spep2us0CWZiButV6u4/nJyRqQozTEuo83z0CR/5cos=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/compiler-interface/1.9.6";
  };

  "org.scala-sbt_core-macros_2.13-1.10.7" = fetchMaven {
    name = "org.scala-sbt_core-macros_2.13-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/core-macros_2.13/1.10.7/core-macros_2.13-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/core-macros_2.13/1.10.7/core-macros_2.13-1.10.7.pom" ];
    hash = "sha256-rsDP4K+yiTgLhmdDP7G5iL3i43v+Dwki9pKXPeWUp4c=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/core-macros_2.13/1.10.7";
  };

  "org.scala-sbt_io_2.13-1.10.4" = fetchMaven {
    name = "org.scala-sbt_io_2.13-1.10.4";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/io_2.13/1.10.4/io_2.13-1.10.4.jar" "https://repo1.maven.org/maven2/org/scala-sbt/io_2.13/1.10.4/io_2.13-1.10.4.pom" ];
    hash = "sha256-vzNWT68yTi1qKz0FT/mGmQ+MTxUyHcW6tOFjXy3AjNc=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/io_2.13/1.10.4";
  };

  "org.scala-sbt_launcher-interface-1.4.4" = fetchMaven {
    name = "org.scala-sbt_launcher-interface-1.4.4";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/launcher-interface/1.4.4/launcher-interface-1.4.4.jar" "https://repo1.maven.org/maven2/org/scala-sbt/launcher-interface/1.4.4/launcher-interface-1.4.4.pom" ];
    hash = "sha256-HWiEWRS8Grm7uQME6o7FYZFhWvJgvrvyxKXMATB0Z7E=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/launcher-interface/1.4.4";
  };

  "org.scala-sbt_sbinary_2.13-0.5.1" = fetchMaven {
    name = "org.scala-sbt_sbinary_2.13-0.5.1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/sbinary_2.13/0.5.1/sbinary_2.13-0.5.1.jar" "https://repo1.maven.org/maven2/org/scala-sbt/sbinary_2.13/0.5.1/sbinary_2.13-0.5.1.pom" ];
    hash = "sha256-+TrjPjSy8WVXq3IYHkHHIzttvHQbgwMLkwwWBys/ryw=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/sbinary_2.13/0.5.1";
  };

  "org.scala-sbt_test-interface-1.0" = fetchMaven {
    name = "org.scala-sbt_test-interface-1.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/test-interface/1.0/test-interface-1.0.jar" "https://repo1.maven.org/maven2/org/scala-sbt/test-interface/1.0/test-interface-1.0.pom" ];
    hash = "sha256-Cc5Q+4mULLHRdw+7Wjx6spCLbKrckXHeNYjIibw4LWw=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/test-interface/1.0";
  };

  "org.scala-sbt_util-control_2.13-1.10.7" = fetchMaven {
    name = "org.scala-sbt_util-control_2.13-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/util-control_2.13/1.10.7/util-control_2.13-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/util-control_2.13/1.10.7/util-control_2.13-1.10.7.pom" ];
    hash = "sha256-CCG/nXpVyd7YrtCYr47tPYIQs/G6vzb/3fCyZ21drhM=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/util-control_2.13/1.10.7";
  };

  "org.scala-sbt_util-interface-1.10.7" = fetchMaven {
    name = "org.scala-sbt_util-interface-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/util-interface/1.10.7/util-interface-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/util-interface/1.10.7/util-interface-1.10.7.pom" ];
    hash = "sha256-cIOD5+vCDptOP6jwds5yG+23h2H54npBzGu3jrCQlvQ=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/util-interface/1.10.7";
  };

  "org.scala-sbt_util-interface-1.9.8" = fetchMaven {
    name = "org.scala-sbt_util-interface-1.9.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/util-interface/1.9.8/util-interface-1.9.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/util-interface/1.9.8/util-interface-1.9.8.pom" ];
    hash = "sha256-7PoE3Jj8JSBaNeK3IzCSlkwArEWP1Zo+XBn0OorE1I8=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/util-interface/1.9.8";
  };

  "org.scala-sbt_util-logging_2.13-1.10.7" = fetchMaven {
    name = "org.scala-sbt_util-logging_2.13-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/util-logging_2.13/1.10.7/util-logging_2.13-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/util-logging_2.13/1.10.7/util-logging_2.13-1.10.7.pom" ];
    hash = "sha256-WfmccbZodef+h77nl7kEe6VxAsyzYlaHudZX0iyTRAs=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/util-logging_2.13/1.10.7";
  };

  "org.scala-sbt_util-position_2.13-1.10.7" = fetchMaven {
    name = "org.scala-sbt_util-position_2.13-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/util-position_2.13/1.10.7/util-position_2.13-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/util-position_2.13/1.10.7/util-position_2.13-1.10.7.pom" ];
    hash = "sha256-hhRemdHTn5rI6IpViSG7KUxU/F2idL0AQf9CdNrF6xA=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/util-position_2.13/1.10.7";
  };

  "org.scala-sbt_util-relation_2.13-1.10.7" = fetchMaven {
    name = "org.scala-sbt_util-relation_2.13-1.10.7";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/util-relation_2.13/1.10.7/util-relation_2.13-1.10.7.jar" "https://repo1.maven.org/maven2/org/scala-sbt/util-relation_2.13/1.10.7/util-relation_2.13-1.10.7.pom" ];
    hash = "sha256-r2kRBeuvusfdZwqZsRRuwp1Sr1PjWDuchmXbVPcSUOM=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/util-relation_2.13/1.10.7";
  };

  "org.scala-sbt_zinc-apiinfo_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-apiinfo_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-apiinfo_2.13/1.10.8/zinc-apiinfo_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-apiinfo_2.13/1.10.8/zinc-apiinfo_2.13-1.10.8.pom" ];
    hash = "sha256-dQKHhRBNfq1miC3UHGlKcSk+P17h+RkQrhiAf7iTbs4=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-apiinfo_2.13/1.10.8";
  };

  "org.scala-sbt_zinc-classfile_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-classfile_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-classfile_2.13/1.10.8/zinc-classfile_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-classfile_2.13/1.10.8/zinc-classfile_2.13-1.10.8.pom" ];
    hash = "sha256-q1mFwkubTGOYvvhay3raXwTMrlbT5hW4DjBRwi8Kc2k=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-classfile_2.13/1.10.8";
  };

  "org.scala-sbt_zinc-classpath_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-classpath_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-classpath_2.13/1.10.8/zinc-classpath_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-classpath_2.13/1.10.8/zinc-classpath_2.13-1.10.8.pom" ];
    hash = "sha256-g1G/PUqwsINONwde2tyZghs2jllmpBMWfDRKFRUA7Rw=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-classpath_2.13/1.10.8";
  };

  "org.scala-sbt_zinc-compile-core_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-compile-core_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-compile-core_2.13/1.10.8/zinc-compile-core_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-compile-core_2.13/1.10.8/zinc-compile-core_2.13-1.10.8.pom" ];
    hash = "sha256-gUSjQRk43fhsUy/3hUW1mxW1/zMsdcgQSA2TifleSG8=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-compile-core_2.13/1.10.8";
  };

  "org.scala-sbt_zinc-core_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-core_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-core_2.13/1.10.8/zinc-core_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-core_2.13/1.10.8/zinc-core_2.13-1.10.8.pom" ];
    hash = "sha256-MhUEFKxdfRj6QnNZjMDzzj1q+b4+7jS/ngjgzTr23co=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-core_2.13/1.10.8";
  };

  "org.scala-sbt_zinc-persist-core-assembly-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-persist-core-assembly-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-persist-core-assembly/1.10.8/zinc-persist-core-assembly-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-persist-core-assembly/1.10.8/zinc-persist-core-assembly-1.10.8.pom" ];
    hash = "sha256-khEFyxGqn013FEwrpkYYTBHxVh30expD1ONPNTdaJDg=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-persist-core-assembly/1.10.8";
  };

  "org.scala-sbt_zinc-persist_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc-persist_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc-persist_2.13/1.10.8/zinc-persist_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc-persist_2.13/1.10.8/zinc-persist_2.13-1.10.8.pom" ];
    hash = "sha256-d+jrvgb6KaT/h2ULKkBjTBH2JimDVNyYRH3C6f+x4YI=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc-persist_2.13/1.10.8";
  };

  "org.scala-sbt_zinc_2.13-1.10.8" = fetchMaven {
    name = "org.scala-sbt_zinc_2.13-1.10.8";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/zinc_2.13/1.10.8/zinc_2.13-1.10.8.jar" "https://repo1.maven.org/maven2/org/scala-sbt/zinc_2.13/1.10.8/zinc_2.13-1.10.8.pom" ];
    hash = "sha256-ozVQW/gVfUe94IdXN49iweDLpA55fhytlDbU607qjTI=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/zinc_2.13/1.10.8";
  };

  "org.scalameta_common_2.13-4.13.4" = fetchMaven {
    name = "org.scalameta_common_2.13-4.13.4";
    urls = [ "https://repo1.maven.org/maven2/org/scalameta/common_2.13/4.13.4/common_2.13-4.13.4.jar" "https://repo1.maven.org/maven2/org/scalameta/common_2.13/4.13.4/common_2.13-4.13.4.pom" ];
    hash = "sha256-MkNrGXJA6y+YmmP4jKpuaNzNCyl29W1I/3HzXFMTeGA=";
    installPath = "https/repo1.maven.org/maven2/org/scalameta/common_2.13/4.13.4";
  };

  "org.scalameta_io_2.13-4.13.4" = fetchMaven {
    name = "org.scalameta_io_2.13-4.13.4";
    urls = [ "https://repo1.maven.org/maven2/org/scalameta/io_2.13/4.13.4/io_2.13-4.13.4.jar" "https://repo1.maven.org/maven2/org/scalameta/io_2.13/4.13.4/io_2.13-4.13.4.pom" ];
    hash = "sha256-VCiXF21t8m2UZA/ADiifzbXbBDh6asbwOyUDf8DnAyc=";
    installPath = "https/repo1.maven.org/maven2/org/scalameta/io_2.13/4.13.4";
  };

  "org.scalameta_parsers_2.13-4.13.4" = fetchMaven {
    name = "org.scalameta_parsers_2.13-4.13.4";
    urls = [ "https://repo1.maven.org/maven2/org/scalameta/parsers_2.13/4.13.4/parsers_2.13-4.13.4.jar" "https://repo1.maven.org/maven2/org/scalameta/parsers_2.13/4.13.4/parsers_2.13-4.13.4.pom" ];
    hash = "sha256-IkSPeAjaFxJoFLqbdS88ulVzCMNB7I/RX4ojcKCsJsw=";
    installPath = "https/repo1.maven.org/maven2/org/scalameta/parsers_2.13/4.13.4";
  };

  "org.scalameta_scalameta_2.13-4.13.4" = fetchMaven {
    name = "org.scalameta_scalameta_2.13-4.13.4";
    urls = [ "https://repo1.maven.org/maven2/org/scalameta/scalameta_2.13/4.13.4/scalameta_2.13-4.13.4.jar" "https://repo1.maven.org/maven2/org/scalameta/scalameta_2.13/4.13.4/scalameta_2.13-4.13.4.pom" ];
    hash = "sha256-+wgBf6HDz3jBsu+Bt7Le3LDl7aNi9LwBAVQg37OeUTY=";
    installPath = "https/repo1.maven.org/maven2/org/scalameta/scalameta_2.13/4.13.4";
  };

  "org.scalameta_semanticdb-shared_2.13-4.13.4" = fetchMaven {
    name = "org.scalameta_semanticdb-shared_2.13-4.13.4";
    urls = [ "https://repo1.maven.org/maven2/org/scalameta/semanticdb-shared_2.13/4.13.4/semanticdb-shared_2.13-4.13.4.jar" "https://repo1.maven.org/maven2/org/scalameta/semanticdb-shared_2.13/4.13.4/semanticdb-shared_2.13-4.13.4.pom" ];
    hash = "sha256-iZwrrosdHE5Di2iXwaV6WuYoGDtmCkKwyunsVQ1J7zU=";
    installPath = "https/repo1.maven.org/maven2/org/scalameta/semanticdb-shared_2.13/4.13.4";
  };

  "org.scalameta_trees_2.13-4.13.4" = fetchMaven {
    name = "org.scalameta_trees_2.13-4.13.4";
    urls = [ "https://repo1.maven.org/maven2/org/scalameta/trees_2.13/4.13.4/trees_2.13-4.13.4.jar" "https://repo1.maven.org/maven2/org/scalameta/trees_2.13/4.13.4/trees_2.13-4.13.4.pom" ];
    hash = "sha256-zVCT+GN7tmTOMu0rYq38GOg5OfqzzeuUeNfHZZf/btQ=";
    installPath = "https/repo1.maven.org/maven2/org/scalameta/trees_2.13/4.13.4";
  };

  "org.slf4j_jcl-over-slf4j-1.7.30" = fetchMaven {
    name = "org.slf4j_jcl-over-slf4j-1.7.30";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/jcl-over-slf4j/1.7.30/jcl-over-slf4j-1.7.30.jar" "https://repo1.maven.org/maven2/org/slf4j/jcl-over-slf4j/1.7.30/jcl-over-slf4j-1.7.30.pom" ];
    hash = "sha256-kCzoxU+HfO0P4FhST+3SNgi23+nCAQOAvw5/XHssymY=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/jcl-over-slf4j/1.7.30";
  };

  "org.slf4j_jul-to-slf4j-1.7.30" = fetchMaven {
    name = "org.slf4j_jul-to-slf4j-1.7.30";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/jul-to-slf4j/1.7.30/jul-to-slf4j-1.7.30.jar" "https://repo1.maven.org/maven2/org/slf4j/jul-to-slf4j/1.7.30/jul-to-slf4j-1.7.30.pom" ];
    hash = "sha256-j+ngBYFB+jb0nMfdiyjuVtUM/lpGs5cAm2x62Z1Y+6Q=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/jul-to-slf4j/1.7.30";
  };

  "org.slf4j_slf4j-api-2.0.17" = fetchMaven {
    name = "org.slf4j_slf4j-api-2.0.17";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/slf4j-api/2.0.17/slf4j-api-2.0.17.jar" "https://repo1.maven.org/maven2/org/slf4j/slf4j-api/2.0.17/slf4j-api-2.0.17.pom" ];
    hash = "sha256-H8Tq0N+icmvASnUUTYYRCm5dhYy03Jqvbz/pWYut/h0=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/slf4j-api/2.0.17";
  };

  "org.slf4j_slf4j-bom-2.0.16" = fetchMaven {
    name = "org.slf4j_slf4j-bom-2.0.16";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/slf4j-bom/2.0.16/slf4j-bom-2.0.16.pom" ];
    hash = "sha256-57CmnZTTjeAyWOFnpSVmPT8waKxeOQosvvyHZDdDHg0=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/slf4j-bom/2.0.16";
  };

  "org.slf4j_slf4j-bom-2.0.17" = fetchMaven {
    name = "org.slf4j_slf4j-bom-2.0.17";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/slf4j-bom/2.0.17/slf4j-bom-2.0.17.pom" ];
    hash = "sha256-qzVo4Yw93XWPRmfJurfoPZ/b9JSCgRngTQmCG6cRwMA=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/slf4j-bom/2.0.17";
  };

  "org.slf4j_slf4j-parent-1.7.30" = fetchMaven {
    name = "org.slf4j_slf4j-parent-1.7.30";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/slf4j-parent/1.7.30/slf4j-parent-1.7.30.pom" ];
    hash = "sha256-poyNibR9n/DHgo+I/r5Qb4ZXkeeiEDT9ZvLLwX1PgeI=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/slf4j-parent/1.7.30";
  };

  "org.slf4j_slf4j-parent-2.0.17" = fetchMaven {
    name = "org.slf4j_slf4j-parent-2.0.17";
    urls = [ "https://repo1.maven.org/maven2/org/slf4j/slf4j-parent/2.0.17/slf4j-parent-2.0.17.pom" ];
    hash = "sha256-H/5UPMMiEV8gCId3abw3znMuG9wWYSMevo6t1zUGACw=";
    installPath = "https/repo1.maven.org/maven2/org/slf4j/slf4j-parent/2.0.17";
  };

  "org.snakeyaml_snakeyaml-engine-2.9" = fetchMaven {
    name = "org.snakeyaml_snakeyaml-engine-2.9";
    urls = [ "https://repo1.maven.org/maven2/org/snakeyaml/snakeyaml-engine/2.9/snakeyaml-engine-2.9.jar" "https://repo1.maven.org/maven2/org/snakeyaml/snakeyaml-engine/2.9/snakeyaml-engine-2.9.pom" ];
    hash = "sha256-KXCxBoxiXcDjRq/fYoEUgW/oxNtqYNSUOFFgVzqG8TM=";
    installPath = "https/repo1.maven.org/maven2/org/snakeyaml/snakeyaml-engine/2.9";
  };

  "org.springframework_spring-framework-bom-5.3.39" = fetchMaven {
    name = "org.springframework_spring-framework-bom-5.3.39";
    urls = [ "https://repo1.maven.org/maven2/org/springframework/spring-framework-bom/5.3.39/spring-framework-bom-5.3.39.pom" ];
    hash = "sha256-V+sR9AvokPz2NrvEFCxdLHl3jrW2o9dP3gisCDAUUDA=";
    installPath = "https/repo1.maven.org/maven2/org/springframework/spring-framework-bom/5.3.39";
  };

  "org.testcontainers_testcontainers-bom-1.20.4" = fetchMaven {
    name = "org.testcontainers_testcontainers-bom-1.20.4";
    urls = [ "https://repo1.maven.org/maven2/org/testcontainers/testcontainers-bom/1.20.4/testcontainers-bom-1.20.4.pom" ];
    hash = "sha256-yavsJKtF6CSRlOeCgZY/Zik+Qiqv1gZvtj367B6buiM=";
    installPath = "https/repo1.maven.org/maven2/org/testcontainers/testcontainers-bom/1.20.4";
  };

  "org.tukaani_xz-1.9" = fetchMaven {
    name = "org.tukaani_xz-1.9";
    urls = [ "https://repo1.maven.org/maven2/org/tukaani/xz/1.9/xz-1.9.jar" "https://repo1.maven.org/maven2/org/tukaani/xz/1.9/xz-1.9.pom" ];
    hash = "sha256-qS7mXrLbWChlkYWhtNTIEPFzgTW6ZMdLoD2a2HzwrHo=";
    installPath = "https/repo1.maven.org/maven2/org/tukaani/xz/1.9";
  };

  "org.yaml_snakeyaml-2.0" = fetchMaven {
    name = "org.yaml_snakeyaml-2.0";
    urls = [ "https://repo1.maven.org/maven2/org/yaml/snakeyaml/2.0/snakeyaml-2.0.jar" "https://repo1.maven.org/maven2/org/yaml/snakeyaml/2.0/snakeyaml-2.0.pom" ];
    hash = "sha256-4/5l8lMWWNxqv1JGr0n8QtEo0KGAUGULj7lmdy9TODI=";
    installPath = "https/repo1.maven.org/maven2/org/yaml/snakeyaml/2.0";
  };

  "ch.epfl.scala_bsp4j-2.2.0-M2" = fetchMaven {
    name = "ch.epfl.scala_bsp4j-2.2.0-M2";
    urls = [ "https://repo1.maven.org/maven2/ch/epfl/scala/bsp4j/2.2.0-M2/bsp4j-2.2.0-M2.jar" "https://repo1.maven.org/maven2/ch/epfl/scala/bsp4j/2.2.0-M2/bsp4j-2.2.0-M2.pom" ];
    hash = "sha256-p9YcDs64uhLxgsiPpx7xhTwhifvU5YdsBSs5dq5NWzU=";
    installPath = "https/repo1.maven.org/maven2/ch/epfl/scala/bsp4j/2.2.0-M2";
  };

  "ch.qos.logback_logback-classic-1.5.17" = fetchMaven {
    name = "ch.qos.logback_logback-classic-1.5.17";
    urls = [ "https://repo1.maven.org/maven2/ch/qos/logback/logback-classic/1.5.17/logback-classic-1.5.17.jar" "https://repo1.maven.org/maven2/ch/qos/logback/logback-classic/1.5.17/logback-classic-1.5.17.pom" ];
    hash = "sha256-2UNtyC/4WXGkwBpDZFDUOkoGcjpuIw8RdraACNmRGP4=";
    installPath = "https/repo1.maven.org/maven2/ch/qos/logback/logback-classic/1.5.17";
  };

  "ch.qos.logback_logback-core-1.5.17" = fetchMaven {
    name = "ch.qos.logback_logback-core-1.5.17";
    urls = [ "https://repo1.maven.org/maven2/ch/qos/logback/logback-core/1.5.17/logback-core-1.5.17.jar" "https://repo1.maven.org/maven2/ch/qos/logback/logback-core/1.5.17/logback-core-1.5.17.pom" ];
    hash = "sha256-stNaZq/vbROKPl6xjrPiVjEAJgZRtFuraihUIpkMkqI=";
    installPath = "https/repo1.maven.org/maven2/ch/qos/logback/logback-core/1.5.17";
  };

  "ch.qos.logback_logback-parent-1.5.17" = fetchMaven {
    name = "ch.qos.logback_logback-parent-1.5.17";
    urls = [ "https://repo1.maven.org/maven2/ch/qos/logback/logback-parent/1.5.17/logback-parent-1.5.17.pom" ];
    hash = "sha256-Am6l31ZT8t57OMENsJtYBbrLOoHJTnl5H5mo5OcyZIc=";
    installPath = "https/repo1.maven.org/maven2/ch/qos/logback/logback-parent/1.5.17";
  };

  "com.fasterxml.jackson_jackson-base-2.12.1" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-base-2.12.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-base/2.12.1/jackson-base-2.12.1.pom" ];
    hash = "sha256-QdwEWejSbiS//t8L9WxLqUxc0QQMY90a7ckBf6YzS2M=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-base/2.12.1";
  };

  "com.fasterxml.jackson_jackson-base-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-base-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-base/2.15.1/jackson-base-2.15.1.pom" ];
    hash = "sha256-DEG+wnRgBDaKE+g5oWHRRWcpgUH3rSj+eex3MKkiDYA=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-base/2.15.1";
  };

  "com.fasterxml.jackson_jackson-bom-2.12.1" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-bom-2.12.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.12.1/jackson-bom-2.12.1.pom" ];
    hash = "sha256-IVTSEkQzRB352EzD1i+FXx8n+HSzPMD5TGq4Ez0VTzc=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.12.1";
  };

  "com.fasterxml.jackson_jackson-bom-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-bom-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.15.1/jackson-bom-2.15.1.pom" ];
    hash = "sha256-xTY1hTkw6E3dYAMDZnockm2fm43WPMcIRt0k2oxO2O8=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.15.1";
  };

  "com.fasterxml.jackson_jackson-bom-2.17.2" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-bom-2.17.2";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.17.2/jackson-bom-2.17.2.pom" ];
    hash = "sha256-uAhCPZKxSJE8I5PhUlyXZOF9QVS/Xh+BQiYGmUYA86E=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.17.2";
  };

  "com.fasterxml.jackson_jackson-bom-2.18.2" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-bom-2.18.2";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.18.2/jackson-bom-2.18.2.pom" ];
    hash = "sha256-zlMHW6EQjXX1QrKglhNEmTuf3hRA6LNpzBcoh3FGWxY=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-bom/2.18.2";
  };

  "com.fasterxml.jackson_jackson-parent-2.12" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-parent-2.12";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.12/jackson-parent-2.12.pom" ];
    hash = "sha256-1XZX837v+3OgmuIWerAxNmHU3KA9W6GDs10dtM+w11o=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.12";
  };

  "com.fasterxml.jackson_jackson-parent-2.15" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-parent-2.15";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.15/jackson-parent-2.15.pom" ];
    hash = "sha256-Rybw8nineMf0Xjlc5GhV4ayVQMYocW1rCXiNhgdXiXc=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.15";
  };

  "com.fasterxml.jackson_jackson-parent-2.17" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-parent-2.17";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.17/jackson-parent-2.17.pom" ];
    hash = "sha256-bwpdlIPUrYpG6AmpG+vbSgz7gRpEaUy7i1k2ZxRlYGc=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.17";
  };

  "com.fasterxml.jackson_jackson-parent-2.18.1" = fetchMaven {
    name = "com.fasterxml.jackson_jackson-parent-2.18.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.18.1/jackson-parent-2.18.1.pom" ];
    hash = "sha256-jogHcaIlfuIF8p3Pn6pQ7VJGEx1aKhBFLVdg2l+coOQ=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/jackson-parent/2.18.1";
  };

  "com.github.luben_zstd-jni-1.5.7-3" = fetchMaven {
    name = "com.github.luben_zstd-jni-1.5.7-3";
    urls = [ "https://repo1.maven.org/maven2/com/github/luben/zstd-jni/1.5.7-3/zstd-jni-1.5.7-3.jar" "https://repo1.maven.org/maven2/com/github/luben/zstd-jni/1.5.7-3/zstd-jni-1.5.7-3.pom" ];
    hash = "sha256-ZtGRbHeRTryX08KHULgZjxtFIb6josIj9adArREhWrg=";
    installPath = "https/repo1.maven.org/maven2/com/github/luben/zstd-jni/1.5.7-3";
  };

  "com.google.errorprone_error_prone_annotations-2.3.4" = fetchMaven {
    name = "com.google.errorprone_error_prone_annotations-2.3.4";
    urls = [ "https://repo1.maven.org/maven2/com/google/errorprone/error_prone_annotations/2.3.4/error_prone_annotations-2.3.4.jar" "https://repo1.maven.org/maven2/com/google/errorprone/error_prone_annotations/2.3.4/error_prone_annotations-2.3.4.pom" ];
    hash = "sha256-lsmKtYyT0ixMTcOraUgQvuXtvvpD/+1V5ppFbqIxkYY=";
    installPath = "https/repo1.maven.org/maven2/com/google/errorprone/error_prone_annotations/2.3.4";
  };

  "com.google.errorprone_error_prone_parent-2.3.4" = fetchMaven {
    name = "com.google.errorprone_error_prone_parent-2.3.4";
    urls = [ "https://repo1.maven.org/maven2/com/google/errorprone/error_prone_parent/2.3.4/error_prone_parent-2.3.4.pom" ];
    hash = "sha256-I+JawBdKiWy7ZcW8vISstkifqGhjqrKpPLgQsKMNl94=";
    installPath = "https/repo1.maven.org/maven2/com/google/errorprone/error_prone_parent/2.3.4";
  };

  "com.google.guava_failureaccess-1.0.1" = fetchMaven {
    name = "com.google.guava_failureaccess-1.0.1";
    urls = [ "https://repo1.maven.org/maven2/com/google/guava/failureaccess/1.0.1/failureaccess-1.0.1.jar" "https://repo1.maven.org/maven2/com/google/guava/failureaccess/1.0.1/failureaccess-1.0.1.pom" ];
    hash = "sha256-keXAVKG0tjTFYMrmNnwUhTz9Tdvv6YgMTVf3WGPaWmM=";
    installPath = "https/repo1.maven.org/maven2/com/google/guava/failureaccess/1.0.1";
  };

  "com.google.guava_guava-30.1-jre" = fetchMaven {
    name = "com.google.guava_guava-30.1-jre";
    urls = [ "https://repo1.maven.org/maven2/com/google/guava/guava/30.1-jre/guava-30.1-jre.jar" "https://repo1.maven.org/maven2/com/google/guava/guava/30.1-jre/guava-30.1-jre.pom" ];
    hash = "sha256-SILksEdHjUqzx9HshT4MC4yCKHLZ27GI9kw08BUmtXg=";
    installPath = "https/repo1.maven.org/maven2/com/google/guava/guava/30.1-jre";
  };

  "com.google.guava_guava-parent-26.0-android" = fetchMaven {
    name = "com.google.guava_guava-parent-26.0-android";
    urls = [ "https://repo1.maven.org/maven2/com/google/guava/guava-parent/26.0-android/guava-parent-26.0-android.pom" ];
    hash = "sha256-E6Ip+1cPpK0zjeeIs6nlA7UKdoaVt4c+rJic/rZqXmU=";
    installPath = "https/repo1.maven.org/maven2/com/google/guava/guava-parent/26.0-android";
  };

  "com.google.guava_guava-parent-30.1-jre" = fetchMaven {
    name = "com.google.guava_guava-parent-30.1-jre";
    urls = [ "https://repo1.maven.org/maven2/com/google/guava/guava-parent/30.1-jre/guava-parent-30.1-jre.pom" ];
    hash = "sha256-yB95NC1JrIdRkg/+VR6T5N1NbHSIt0v1mLCOqmJ5W3s=";
    installPath = "https/repo1.maven.org/maven2/com/google/guava/guava-parent/30.1-jre";
  };

  "com.google.guava_listenablefuture-9999.0-empty-to-avoid-conflict-with-guava" = fetchMaven {
    name = "com.google.guava_listenablefuture-9999.0-empty-to-avoid-conflict-with-guava";
    urls = [ "https://repo1.maven.org/maven2/com/google/guava/listenablefuture/9999.0-empty-to-avoid-conflict-with-guava/listenablefuture-9999.0-empty-to-avoid-conflict-with-guava.jar" "https://repo1.maven.org/maven2/com/google/guava/listenablefuture/9999.0-empty-to-avoid-conflict-with-guava/listenablefuture-9999.0-empty-to-avoid-conflict-with-guava.pom" ];
    hash = "sha256-RKtfF6GYbf2zSPY1m+gj8UN8qpI0GcTyMCX6xPLTdq8=";
    installPath = "https/repo1.maven.org/maven2/com/google/guava/listenablefuture/9999.0-empty-to-avoid-conflict-with-guava";
  };

  "com.google.j2objc_j2objc-annotations-1.3" = fetchMaven {
    name = "com.google.j2objc_j2objc-annotations-1.3";
    urls = [ "https://repo1.maven.org/maven2/com/google/j2objc/j2objc-annotations/1.3/j2objc-annotations-1.3.jar" "https://repo1.maven.org/maven2/com/google/j2objc/j2objc-annotations/1.3/j2objc-annotations-1.3.pom" ];
    hash = "sha256-66DvifOQZUx1Dp1O4uKA7mylXcgFQOBqcCIL7qVklbI=";
    installPath = "https/repo1.maven.org/maven2/com/google/j2objc/j2objc-annotations/1.3";
  };

  "com.google.protobuf_protobuf-bom-3.19.6" = fetchMaven {
    name = "com.google.protobuf_protobuf-bom-3.19.6";
    urls = [ "https://repo1.maven.org/maven2/com/google/protobuf/protobuf-bom/3.19.6/protobuf-bom-3.19.6.pom" ];
    hash = "sha256-5Zn2CRSfxkcVTun5Ku9MsX23r3Q41JIfdAgq3cebFlQ=";
    installPath = "https/repo1.maven.org/maven2/com/google/protobuf/protobuf-bom/3.19.6";
  };

  "com.google.protobuf_protobuf-java-3.19.6" = fetchMaven {
    name = "com.google.protobuf_protobuf-java-3.19.6";
    urls = [ "https://repo1.maven.org/maven2/com/google/protobuf/protobuf-java/3.19.6/protobuf-java-3.19.6.jar" "https://repo1.maven.org/maven2/com/google/protobuf/protobuf-java/3.19.6/protobuf-java-3.19.6.pom" ];
    hash = "sha256-ud9V+TVS5taqg+rsGRcJu5AgFH9kSzELQsg7E5MlrXs=";
    installPath = "https/repo1.maven.org/maven2/com/google/protobuf/protobuf-java/3.19.6";
  };

  "com.google.protobuf_protobuf-parent-3.19.6" = fetchMaven {
    name = "com.google.protobuf_protobuf-parent-3.19.6";
    urls = [ "https://repo1.maven.org/maven2/com/google/protobuf/protobuf-parent/3.19.6/protobuf-parent-3.19.6.pom" ];
    hash = "sha256-NpkIQhCu4fH9fDWCLDDSlvoGpqmnLJ2rEODcWD69c68=";
    installPath = "https/repo1.maven.org/maven2/com/google/protobuf/protobuf-parent/3.19.6";
  };

  "com.thesamet.scalapb_lenses_2.13-0.11.15" = fetchMaven {
    name = "com.thesamet.scalapb_lenses_2.13-0.11.15";
    urls = [ "https://repo1.maven.org/maven2/com/thesamet/scalapb/lenses_2.13/0.11.15/lenses_2.13-0.11.15.jar" "https://repo1.maven.org/maven2/com/thesamet/scalapb/lenses_2.13/0.11.15/lenses_2.13-0.11.15.pom" ];
    hash = "sha256-Y8wbPEVQSLqQKaUQ0PgQudYNzYLcdUfZY63hRbIosS4=";
    installPath = "https/repo1.maven.org/maven2/com/thesamet/scalapb/lenses_2.13/0.11.15";
  };

  "com.thesamet.scalapb_scalapb-runtime_2.13-0.11.15" = fetchMaven {
    name = "com.thesamet.scalapb_scalapb-runtime_2.13-0.11.15";
    urls = [ "https://repo1.maven.org/maven2/com/thesamet/scalapb/scalapb-runtime_2.13/0.11.15/scalapb-runtime_2.13-0.11.15.jar" "https://repo1.maven.org/maven2/com/thesamet/scalapb/scalapb-runtime_2.13/0.11.15/scalapb-runtime_2.13-0.11.15.pom" ];
    hash = "sha256-aHYA62RiZKbZfBjrvN6kV95pp3nj6H8Q3ctpDM5XfXY=";
    installPath = "https/repo1.maven.org/maven2/com/thesamet/scalapb/scalapb-runtime_2.13/0.11.15";
  };

  "com.vladsch.flexmark_flexmark-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark/0.62.2/flexmark-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark/0.62.2/flexmark-0.62.2.pom" ];
    hash = "sha256-CMbMcOs3cMmCu7+sAh6qiwj63tMDlJ6qIrZRbHF2gDE=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-anchorlink-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-anchorlink-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-anchorlink/0.62.2/flexmark-ext-anchorlink-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-anchorlink/0.62.2/flexmark-ext-anchorlink-0.62.2.pom" ];
    hash = "sha256-weHNR6k/69NjAg2Vs72ce1wOZ1rwBicv4TMLDS9jnGE=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-anchorlink/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-autolink-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-autolink-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-autolink/0.62.2/flexmark-ext-autolink-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-autolink/0.62.2/flexmark-ext-autolink-0.62.2.pom" ];
    hash = "sha256-15OH05RylvbLSzEu47GBdhtKZvyP3ibjXETb+3Sn5+Y=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-autolink/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-emoji-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-emoji-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-emoji/0.62.2/flexmark-ext-emoji-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-emoji/0.62.2/flexmark-ext-emoji-0.62.2.pom" ];
    hash = "sha256-UHbh+WMLnLqFzhE9GIdc3pwFEBy94rNpWT6olRGnIvI=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-emoji/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-gfm-strikethrough-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-gfm-strikethrough-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-gfm-strikethrough/0.62.2/flexmark-ext-gfm-strikethrough-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-gfm-strikethrough/0.62.2/flexmark-ext-gfm-strikethrough-0.62.2.pom" ];
    hash = "sha256-1l/E13+s+Pc/CVD28MVSrqRUkkrfwKD6K0+2zvCQX8o=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-gfm-strikethrough/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-gfm-tasklist-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-gfm-tasklist-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-gfm-tasklist/0.62.2/flexmark-ext-gfm-tasklist-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-gfm-tasklist/0.62.2/flexmark-ext-gfm-tasklist-0.62.2.pom" ];
    hash = "sha256-gtACK+9qTISC22QYuWoyvgNeTXmuSOZxXuojXESKAvE=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-gfm-tasklist/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-ins-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-ins-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-ins/0.62.2/flexmark-ext-ins-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-ins/0.62.2/flexmark-ext-ins-0.62.2.pom" ];
    hash = "sha256-VIKNuMXAxAbmNWnk2nWPgpSzbkoGfpA6miKQuvOUmF4=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-ins/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-superscript-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-superscript-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-superscript/0.62.2/flexmark-ext-superscript-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-superscript/0.62.2/flexmark-ext-superscript-0.62.2.pom" ];
    hash = "sha256-pfRu434uIlDIkwSEaFwxZFwcUjTnU5cbuSfsG578PC4=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-superscript/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-tables-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-tables-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-tables/0.62.2/flexmark-ext-tables-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-tables/0.62.2/flexmark-ext-tables-0.62.2.pom" ];
    hash = "sha256-3Fef3ZHc6jjwTHjvOGsVvLAMbRMwJHlZ5X7SKIaCj6w=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-tables/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-wikilink-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-wikilink-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-wikilink/0.62.2/flexmark-ext-wikilink-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-wikilink/0.62.2/flexmark-ext-wikilink-0.62.2.pom" ];
    hash = "sha256-NQtfUT4F3p6+nGk6o07EwlX1kZvkXarCfWw07QQgYyE=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-wikilink/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-ext-yaml-front-matter-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-ext-yaml-front-matter-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-yaml-front-matter/0.62.2/flexmark-ext-yaml-front-matter-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-yaml-front-matter/0.62.2/flexmark-ext-yaml-front-matter-0.62.2.pom" ];
    hash = "sha256-tc0KpVAhnflMmVlFUXFqwocYsXuL3PiXeFtdO+p9Ta4=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-ext-yaml-front-matter/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-java-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-java-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-java/0.62.2/flexmark-java-0.62.2.pom" ];
    hash = "sha256-DlxcWCry0vUFs1L54guu8FLGgpuYD9+ksL2x5sv6E9c=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-java/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-jira-converter-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-jira-converter-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-jira-converter/0.62.2/flexmark-jira-converter-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-jira-converter/0.62.2/flexmark-jira-converter-0.62.2.pom" ];
    hash = "sha256-k4eeiCIqq4fE5F0MPS9FMDEdlWEb+Gd36pDNxQSFMFY=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-jira-converter/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util/0.62.2/flexmark-util-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util/0.62.2/flexmark-util-0.62.2.pom" ];
    hash = "sha256-A3coPMDIx8qFH4WcoKFEcAY6MDeICS9olH/SPgIEbeI=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-ast-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-ast-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-ast/0.62.2/flexmark-util-ast-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-ast/0.62.2/flexmark-util-ast-0.62.2.pom" ];
    hash = "sha256-bT7Cqm3k63wFdcC63M3WAtz5p0QqArmmCvpfPGuvDjw=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-ast/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-builder-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-builder-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-builder/0.62.2/flexmark-util-builder-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-builder/0.62.2/flexmark-util-builder-0.62.2.pom" ];
    hash = "sha256-+kjX932WxGRANJw+UPDyy8MJB6wKUXI7tf+PyOAYbJM=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-builder/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-collection-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-collection-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-collection/0.62.2/flexmark-util-collection-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-collection/0.62.2/flexmark-util-collection-0.62.2.pom" ];
    hash = "sha256-vsdaPDU/TcTKnim4MAWhcXp4P0upYTWIMLMSCeg6Wx4=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-collection/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-data-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-data-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-data/0.62.2/flexmark-util-data-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-data/0.62.2/flexmark-util-data-0.62.2.pom" ];
    hash = "sha256-m3S05kD1HNXWdGXPwXapNqzLv4g2WicpuaNUJjvZDW4=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-data/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-dependency-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-dependency-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-dependency/0.62.2/flexmark-util-dependency-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-dependency/0.62.2/flexmark-util-dependency-0.62.2.pom" ];
    hash = "sha256-nSFsXZXFD67UbxMv6hAZEjv6VfCmewH9PsP6zk7vLR4=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-dependency/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-format-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-format-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-format/0.62.2/flexmark-util-format-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-format/0.62.2/flexmark-util-format-0.62.2.pom" ];
    hash = "sha256-j7GbAIjjp00wTPbuXCTO//af5J5JooOPmHh2Da3jBd0=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-format/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-html-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-html-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-html/0.62.2/flexmark-util-html-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-html/0.62.2/flexmark-util-html-0.62.2.pom" ];
    hash = "sha256-9MSBM5awDcqrCDRtRKKCrxD35X5DYf+U7NmUR8OOW94=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-html/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-misc-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-misc-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-misc/0.62.2/flexmark-util-misc-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-misc/0.62.2/flexmark-util-misc-0.62.2.pom" ];
    hash = "sha256-VfG2y0OgXWkcDF0VNHFTnOsf1jjmZtSZThZABQ0yc5A=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-misc/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-options-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-options-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-options/0.62.2/flexmark-util-options-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-options/0.62.2/flexmark-util-options-0.62.2.pom" ];
    hash = "sha256-Px6MK19ozVJLQGj3fCpDhMTUtrWLzhiqdDDRdBpf8i8=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-options/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-sequence-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-sequence-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-sequence/0.62.2/flexmark-util-sequence-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-sequence/0.62.2/flexmark-util-sequence-0.62.2.pom" ];
    hash = "sha256-J8ZXFheFBaMP+b9VMZ02j5Sonvtf26k6DR7C5AspxVg=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-sequence/0.62.2";
  };

  "com.vladsch.flexmark_flexmark-util-visitor-0.62.2" = fetchMaven {
    name = "com.vladsch.flexmark_flexmark-util-visitor-0.62.2";
    urls = [ "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-visitor/0.62.2/flexmark-util-visitor-0.62.2.jar" "https://repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-visitor/0.62.2/flexmark-util-visitor-0.62.2.pom" ];
    hash = "sha256-sGUXA1qXnyVQTMPXJoAh4L1+L895QeeW7oazG3/NqyI=";
    installPath = "https/repo1.maven.org/maven2/com/vladsch/flexmark/flexmark-util-visitor/0.62.2";
  };

  "io.get-coursier.jniutils_windows-jni-utils-0.3.3" = fetchMaven {
    name = "io.get-coursier.jniutils_windows-jni-utils-0.3.3";
    urls = [ "https://repo1.maven.org/maven2/io/get-coursier/jniutils/windows-jni-utils/0.3.3/windows-jni-utils-0.3.3.jar" "https://repo1.maven.org/maven2/io/get-coursier/jniutils/windows-jni-utils/0.3.3/windows-jni-utils-0.3.3.pom" ];
    hash = "sha256-OgBT8ULqeyvpNMGSmXrwpYXR4VOAlmSIMs+BejCP56c=";
    installPath = "https/repo1.maven.org/maven2/io/get-coursier/jniutils/windows-jni-utils/0.3.3";
  };

  "io.github.alexarchambault_concurrent-reference-hash-map-1.1.0" = fetchMaven {
    name = "io.github.alexarchambault_concurrent-reference-hash-map-1.1.0";
    urls = [ "https://repo1.maven.org/maven2/io/github/alexarchambault/concurrent-reference-hash-map/1.1.0/concurrent-reference-hash-map-1.1.0.jar" "https://repo1.maven.org/maven2/io/github/alexarchambault/concurrent-reference-hash-map/1.1.0/concurrent-reference-hash-map-1.1.0.pom" ];
    hash = "sha256-949g3dbXxz773bZlkiK2Xh3XiY5Ofc+1k6i8LM6s+yI=";
    installPath = "https/repo1.maven.org/maven2/io/github/alexarchambault/concurrent-reference-hash-map/1.1.0";
  };

  "io.github.alexarchambault_is-terminal-0.1.2" = fetchMaven {
    name = "io.github.alexarchambault_is-terminal-0.1.2";
    urls = [ "https://repo1.maven.org/maven2/io/github/alexarchambault/is-terminal/0.1.2/is-terminal-0.1.2.jar" "https://repo1.maven.org/maven2/io/github/alexarchambault/is-terminal/0.1.2/is-terminal-0.1.2.pom" ];
    hash = "sha256-j9aW4Y/zyD4aYu2XykzfEpdGUXideUCkVTFSvtzlH48=";
    installPath = "https/repo1.maven.org/maven2/io/github/alexarchambault/is-terminal/0.1.2";
  };

  "io.github.classgraph_classgraph-4.8.180" = fetchMaven {
    name = "io.github.classgraph_classgraph-4.8.180";
    urls = [ "https://repo1.maven.org/maven2/io/github/classgraph/classgraph/4.8.180/classgraph-4.8.180.jar" "https://repo1.maven.org/maven2/io/github/classgraph/classgraph/4.8.180/classgraph-4.8.180.pom" ];
    hash = "sha256-shL+VONWBOBL1gf6HvkILdwpGWFv2dW7wG43j5ZPbR4=";
    installPath = "https/repo1.maven.org/maven2/io/github/classgraph/classgraph/4.8.180";
  };

  "io.github.java-diff-utils_java-diff-utils-4.12" = fetchMaven {
    name = "io.github.java-diff-utils_java-diff-utils-4.12";
    urls = [ "https://repo1.maven.org/maven2/io/github/java-diff-utils/java-diff-utils/4.12/java-diff-utils-4.12.jar" "https://repo1.maven.org/maven2/io/github/java-diff-utils/java-diff-utils/4.12/java-diff-utils-4.12.pom" ];
    hash = "sha256-SMNRfv+BvfxjgwFH0fHU16fd1bDn/QMrPQN8Eyb6deA=";
    installPath = "https/repo1.maven.org/maven2/io/github/java-diff-utils/java-diff-utils/4.12";
  };

  "io.github.java-diff-utils_java-diff-utils-parent-4.12" = fetchMaven {
    name = "io.github.java-diff-utils_java-diff-utils-parent-4.12";
    urls = [ "https://repo1.maven.org/maven2/io/github/java-diff-utils/java-diff-utils-parent/4.12/java-diff-utils-parent-4.12.pom" ];
    hash = "sha256-l9MekOAkDQrHpgMMLkbZQJtiaSmyE7h0XneiHciAFOI=";
    installPath = "https/repo1.maven.org/maven2/io/github/java-diff-utils/java-diff-utils-parent/4.12";
  };

  "net.sf.jopt-simple_jopt-simple-5.0.4" = fetchMaven {
    name = "net.sf.jopt-simple_jopt-simple-5.0.4";
    urls = [ "https://repo1.maven.org/maven2/net/sf/jopt-simple/jopt-simple/5.0.4/jopt-simple-5.0.4.jar" "https://repo1.maven.org/maven2/net/sf/jopt-simple/jopt-simple/5.0.4/jopt-simple-5.0.4.pom" ];
    hash = "sha256-/l4TgZ+p8AP432PBNvhoHUw7VjAHgsP7PBKjYnqxFB0=";
    installPath = "https/repo1.maven.org/maven2/net/sf/jopt-simple/jopt-simple/5.0.4";
  };

  "org.apache.commons_commons-compress-1.26.2" = fetchMaven {
    name = "org.apache.commons_commons-compress-1.26.2";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-compress/1.26.2/commons-compress-1.26.2.jar" "https://repo1.maven.org/maven2/org/apache/commons/commons-compress/1.26.2/commons-compress-1.26.2.pom" ];
    hash = "sha256-5D5lx07bmuJYoxLZUVG2SuSIuqwwWux50VCge+WmwiA=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-compress/1.26.2";
  };

  "org.apache.commons_commons-lang3-3.14.0" = fetchMaven {
    name = "org.apache.commons_commons-lang3-3.14.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-lang3/3.14.0/commons-lang3-3.14.0.jar" "https://repo1.maven.org/maven2/org/apache/commons/commons-lang3/3.14.0/commons-lang3-3.14.0.pom" ];
    hash = "sha256-b5ZfCjrVKvpTFeW1SMtspKLtvI/uZuczaizc6Oj0xsI=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-lang3/3.14.0";
  };

  "org.apache.commons_commons-math3-3.2" = fetchMaven {
    name = "org.apache.commons_commons-math3-3.2";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-math3/3.2/commons-math3-3.2.jar" "https://repo1.maven.org/maven2/org/apache/commons/commons-math3/3.2/commons-math3-3.2.pom" ];
    hash = "sha256-0EqwMxOWH5aJIPkq0w1zL+SmdRt4hCUYKKbI1/3y5NU=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-math3/3.2";
  };

  "org.apache.commons_commons-parent-28" = fetchMaven {
    name = "org.apache.commons_commons-parent-28";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-parent/28/commons-parent-28.pom" ];
    hash = "sha256-FVG+Ox8Q+6OJu4zIZNnwjeI6mCunwb9mMvBmC11Wqn0=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-parent/28";
  };

  "org.apache.commons_commons-parent-64" = fetchMaven {
    name = "org.apache.commons_commons-parent-64";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-parent/64/commons-parent-64.pom" ];
    hash = "sha256-Q6095muAB/pbFjv41RzuqBbVSWMz8zN47Okjv96TqWI=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-parent/64";
  };

  "org.apache.commons_commons-parent-69" = fetchMaven {
    name = "org.apache.commons_commons-parent-69";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-parent/69/commons-parent-69.pom" ];
    hash = "sha256-XDFSOofSIPQI87JPu4s21bhzz9SDiYXZ4rIoURJ4feI=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-parent/69";
  };

  "org.apache.commons_commons-parent-78" = fetchMaven {
    name = "org.apache.commons_commons-parent-78";
    urls = [ "https://repo1.maven.org/maven2/org/apache/commons/commons-parent/78/commons-parent-78.pom" ];
    hash = "sha256-0aJAoMZMen5VZmg8WT/tz9MMHFaXx6DgdiAVpYrCsac=";
    installPath = "https/repo1.maven.org/maven2/org/apache/commons/commons-parent/78";
  };

  "org.apache.cxf_cxf-4.0.6" = fetchMaven {
    name = "org.apache.cxf_cxf-4.0.6";
    urls = [ "https://repo1.maven.org/maven2/org/apache/cxf/cxf/4.0.6/cxf-4.0.6.pom" ];
    hash = "sha256-P/nmU+pQ5HiJp0i3fqQVYypc+1AFeWCdOBGozTZRiSM=";
    installPath = "https/repo1.maven.org/maven2/org/apache/cxf/cxf/4.0.6";
  };

  "org.apache.cxf_cxf-bom-4.0.6" = fetchMaven {
    name = "org.apache.cxf_cxf-bom-4.0.6";
    urls = [ "https://repo1.maven.org/maven2/org/apache/cxf/cxf-bom/4.0.6/cxf-bom-4.0.6.pom" ];
    hash = "sha256-w1H9G+T3S+LWfJ/dVX7JnLwPsi3tGJlFHlde0ZyKVE4=";
    installPath = "https/repo1.maven.org/maven2/org/apache/cxf/cxf-bom/4.0.6";
  };

  "org.apache.groovy_groovy-bom-4.0.22" = fetchMaven {
    name = "org.apache.groovy_groovy-bom-4.0.22";
    urls = [ "https://repo1.maven.org/maven2/org/apache/groovy/groovy-bom/4.0.22/groovy-bom-4.0.22.pom" ];
    hash = "sha256-9hsejVx5kj/oQtf+JvuKqOuzRfJIJbPoys04ArDEu9o=";
    installPath = "https/repo1.maven.org/maven2/org/apache/groovy/groovy-bom/4.0.22";
  };

  "org.apache.logging_logging-parent-11.3.0" = fetchMaven {
    name = "org.apache.logging_logging-parent-11.3.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/logging/logging-parent/11.3.0/logging-parent-11.3.0.pom" ];
    hash = "sha256-06rPgZ5cRXf8cg84KMl7HVR3vcgvV0ThY76UsgAFf+w=";
    installPath = "https/repo1.maven.org/maven2/org/apache/logging/logging-parent/11.3.0";
  };

  "org.apache.tika_tika-core-3.1.0" = fetchMaven {
    name = "org.apache.tika_tika-core-3.1.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/tika/tika-core/3.1.0/tika-core-3.1.0.jar" "https://repo1.maven.org/maven2/org/apache/tika/tika-core/3.1.0/tika-core-3.1.0.pom" ];
    hash = "sha256-NnIdgEccFyNqv8HIciO0d8vVAcbEaQ5typuaYi9aUjo=";
    installPath = "https/repo1.maven.org/maven2/org/apache/tika/tika-core/3.1.0";
  };

  "org.apache.tika_tika-parent-3.1.0" = fetchMaven {
    name = "org.apache.tika_tika-parent-3.1.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/tika/tika-parent/3.1.0/tika-parent-3.1.0.pom" ];
    hash = "sha256-r4SO6kcvuQSLepEsjrJmnGOQ7cyAjpxRVvc4krj6Sh4=";
    installPath = "https/repo1.maven.org/maven2/org/apache/tika/tika-parent/3.1.0";
  };

  "org.apache.xbean_xbean-3.7" = fetchMaven {
    name = "org.apache.xbean_xbean-3.7";
    urls = [ "https://repo1.maven.org/maven2/org/apache/xbean/xbean/3.7/xbean-3.7.pom" ];
    hash = "sha256-7moEcdxl+B1i7xstWBlWabSFr9QLszuciySggKYvpAE=";
    installPath = "https/repo1.maven.org/maven2/org/apache/xbean/xbean/3.7";
  };

  "org.apache.xbean_xbean-reflect-3.7" = fetchMaven {
    name = "org.apache.xbean_xbean-reflect-3.7";
    urls = [ "https://repo1.maven.org/maven2/org/apache/xbean/xbean-reflect/3.7/xbean-reflect-3.7.jar" "https://repo1.maven.org/maven2/org/apache/xbean/xbean-reflect/3.7/xbean-reflect-3.7.pom" ];
    hash = "sha256-Zp97nk/YwipUj92NnhjU5tKNXgUmPWh2zWic2FoS434=";
    installPath = "https/repo1.maven.org/maven2/org/apache/xbean/xbean-reflect/3.7";
  };

  "org.codehaus.plexus_plexus-17" = fetchMaven {
    name = "org.codehaus.plexus_plexus-17";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus/17/plexus-17.pom" ];
    hash = "sha256-IeF8wVVWksgiGA2oX3NdIalO+qYNKpGcqY2hVOBKGy4=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus/17";
  };

  "org.codehaus.plexus_plexus-18" = fetchMaven {
    name = "org.codehaus.plexus_plexus-18";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus/18/plexus-18.pom" ];
    hash = "sha256-MW5t8h+IK6i4Gm58Lz3ucsEXD1GRupWWNKcizh2Osr0=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus/18";
  };

  "org.codehaus.plexus_plexus-5.1" = fetchMaven {
    name = "org.codehaus.plexus_plexus-5.1";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus/5.1/plexus-5.1.pom" ];
    hash = "sha256-ywTicwjHcL7BzKPO3XzXpc9pE0M0j7Khcop85G3XqDI=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus/5.1";
  };

  "org.codehaus.plexus_plexus-6.5" = fetchMaven {
    name = "org.codehaus.plexus_plexus-6.5";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus/6.5/plexus-6.5.pom" ];
    hash = "sha256-6Hhmat92ApFn7ze2iYyOusDxXMYp98v1GNqAvKypKSQ=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus/6.5";
  };

  "org.codehaus.plexus_plexus-archiver-4.10.0" = fetchMaven {
    name = "org.codehaus.plexus_plexus-archiver-4.10.0";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-archiver/4.10.0/plexus-archiver-4.10.0.jar" "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-archiver/4.10.0/plexus-archiver-4.10.0.pom" ];
    hash = "sha256-pp9ZIBwMabdHgJHVXZ4eHUFTXevlLlGjMV8Cr9jdz5E=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus-archiver/4.10.0";
  };

  "org.codehaus.plexus_plexus-classworlds-2.6.0" = fetchMaven {
    name = "org.codehaus.plexus_plexus-classworlds-2.6.0";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-classworlds/2.6.0/plexus-classworlds-2.6.0.jar" "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-classworlds/2.6.0/plexus-classworlds-2.6.0.pom" ];
    hash = "sha256-vh7/TKxdcZVxXljM5MLGppoP0Bc28QyI/WsrPc6XSEA=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus-classworlds/2.6.0";
  };

  "org.codehaus.plexus_plexus-container-default-2.1.1" = fetchMaven {
    name = "org.codehaus.plexus_plexus-container-default-2.1.1";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-container-default/2.1.1/plexus-container-default-2.1.1.jar" "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-container-default/2.1.1/plexus-container-default-2.1.1.pom" ];
    hash = "sha256-E0Dt5DQRVlxg8fddMJZpvhU5cfNwB9MJTi/GJ1PVt3A=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus-container-default/2.1.1";
  };

  "org.codehaus.plexus_plexus-containers-2.1.1" = fetchMaven {
    name = "org.codehaus.plexus_plexus-containers-2.1.1";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-containers/2.1.1/plexus-containers-2.1.1.pom" ];
    hash = "sha256-LR5FBjo4qAjwjKpHajTnuUBN7cLKbeTJRtYYc8q4FNw=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus-containers/2.1.1";
  };

  "org.codehaus.plexus_plexus-io-3.5.0" = fetchMaven {
    name = "org.codehaus.plexus_plexus-io-3.5.0";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-io/3.5.0/plexus-io-3.5.0.jar" "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-io/3.5.0/plexus-io-3.5.0.pom" ];
    hash = "sha256-GrKvyvvG9jqNcHXTOaBd+QWRUZCWORyrgu+jbgJbWpg=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus-io/3.5.0";
  };

  "org.codehaus.plexus_plexus-utils-4.0.1" = fetchMaven {
    name = "org.codehaus.plexus_plexus-utils-4.0.1";
    urls = [ "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-utils/4.0.1/plexus-utils-4.0.1.jar" "https://repo1.maven.org/maven2/org/codehaus/plexus/plexus-utils/4.0.1/plexus-utils-4.0.1.pom" ];
    hash = "sha256-bMqrl8EEfcmwl4D8hK7iaYROM0j9/RVdEyns9BbWgPM=";
    installPath = "https/repo1.maven.org/maven2/org/codehaus/plexus/plexus-utils/4.0.1";
  };

  "org.eclipse.ee4j_project-1.0.7" = fetchMaven {
    name = "org.eclipse.ee4j_project-1.0.7";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/ee4j/project/1.0.7/project-1.0.7.pom" ];
    hash = "sha256-1HxZiJ0aeo1n8AWjwGKEoPwVFP9kndMBye7xwgYEal8=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/ee4j/project/1.0.7";
  };

  "org.eclipse.jetty_jetty-bom-11.0.24" = fetchMaven {
    name = "org.eclipse.jetty_jetty-bom-11.0.24";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/jetty/jetty-bom/11.0.24/jetty-bom-11.0.24.pom" ];
    hash = "sha256-U5/npTQQwHE+dvi08aq1ZK4s42xgilyPsqXYWrPvdEM=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/jetty/jetty-bom/11.0.24";
  };

  "org.eclipse.lsp4j_org.eclipse.lsp4j.generator-0.20.1" = fetchMaven {
    name = "org.eclipse.lsp4j_org.eclipse.lsp4j.generator-0.20.1";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/lsp4j/org.eclipse.lsp4j.generator/0.20.1/org.eclipse.lsp4j.generator-0.20.1.jar" "https://repo1.maven.org/maven2/org/eclipse/lsp4j/org.eclipse.lsp4j.generator/0.20.1/org.eclipse.lsp4j.generator-0.20.1.pom" ];
    hash = "sha256-YihOE4ZIhHUljdpQd9FATS7AzAkRiATjJz4r4IhsBOs=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/lsp4j/org.eclipse.lsp4j.generator/0.20.1";
  };

  "org.eclipse.lsp4j_org.eclipse.lsp4j.jsonrpc-0.20.1" = fetchMaven {
    name = "org.eclipse.lsp4j_org.eclipse.lsp4j.jsonrpc-0.20.1";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/lsp4j/org.eclipse.lsp4j.jsonrpc/0.20.1/org.eclipse.lsp4j.jsonrpc-0.20.1.jar" "https://repo1.maven.org/maven2/org/eclipse/lsp4j/org.eclipse.lsp4j.jsonrpc/0.20.1/org.eclipse.lsp4j.jsonrpc-0.20.1.pom" ];
    hash = "sha256-lLLBglY2iO5Xm7gfaKHb95jm7Yd2tKI+RUlVIqKSx5U=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/lsp4j/org.eclipse.lsp4j.jsonrpc/0.20.1";
  };

  "org.eclipse.xtend_org.eclipse.xtend.lib-2.28.0" = fetchMaven {
    name = "org.eclipse.xtend_org.eclipse.xtend.lib-2.28.0";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/xtend/org.eclipse.xtend.lib/2.28.0/org.eclipse.xtend.lib-2.28.0.jar" "https://repo1.maven.org/maven2/org/eclipse/xtend/org.eclipse.xtend.lib/2.28.0/org.eclipse.xtend.lib-2.28.0.pom" ];
    hash = "sha256-ch5uYaECYGox+AL4EU0OC614gqTK/IkWmlxCW+FYusU=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/xtend/org.eclipse.xtend.lib/2.28.0";
  };

  "org.eclipse.xtend_org.eclipse.xtend.lib.macro-2.28.0" = fetchMaven {
    name = "org.eclipse.xtend_org.eclipse.xtend.lib.macro-2.28.0";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/xtend/org.eclipse.xtend.lib.macro/2.28.0/org.eclipse.xtend.lib.macro-2.28.0.jar" "https://repo1.maven.org/maven2/org/eclipse/xtend/org.eclipse.xtend.lib.macro/2.28.0/org.eclipse.xtend.lib.macro-2.28.0.pom" ];
    hash = "sha256-xu5Ogojl3XzSTfETwsFodjvZydpdi2jZXY9wu5zMyOQ=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/xtend/org.eclipse.xtend.lib.macro/2.28.0";
  };

  "org.eclipse.xtext_org.eclipse.xtext.xbase.lib-2.28.0" = fetchMaven {
    name = "org.eclipse.xtext_org.eclipse.xtext.xbase.lib-2.28.0";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/xtext/org.eclipse.xtext.xbase.lib/2.28.0/org.eclipse.xtext.xbase.lib-2.28.0.jar" "https://repo1.maven.org/maven2/org/eclipse/xtext/org.eclipse.xtext.xbase.lib/2.28.0/org.eclipse.xtext.xbase.lib-2.28.0.pom" ];
    hash = "sha256-J9fEh2WXIT3xrhzNQZBoYphh2DUrkas0wpJPWhWRvbI=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/xtext/org.eclipse.xtext.xbase.lib/2.28.0";
  };

  "org.eclipse.xtext_xtext-dev-bom-2.28.0" = fetchMaven {
    name = "org.eclipse.xtext_xtext-dev-bom-2.28.0";
    urls = [ "https://repo1.maven.org/maven2/org/eclipse/xtext/xtext-dev-bom/2.28.0/xtext-dev-bom-2.28.0.pom" ];
    hash = "sha256-g4xSwbZW3JjZV+BF16ohvZ+v3o7JkVkv5CsiKT6ixVY=";
    installPath = "https/repo1.maven.org/maven2/org/eclipse/xtext/xtext-dev-bom/2.28.0";
  };

  "org.fusesource.jansi_jansi-2.4.1" = fetchMaven {
    name = "org.fusesource.jansi_jansi-2.4.1";
    urls = [ "https://repo1.maven.org/maven2/org/fusesource/jansi/jansi/2.4.1/jansi-2.4.1.jar" "https://repo1.maven.org/maven2/org/fusesource/jansi/jansi/2.4.1/jansi-2.4.1.pom" ];
    hash = "sha256-M9G+H9TA5eB6NwlBmDP0ghxZzjbvLimPXNRZHyxJXac=";
    installPath = "https/repo1.maven.org/maven2/org/fusesource/jansi/jansi/2.4.1";
  };

  "org.nibor.autolink_autolink-0.6.0" = fetchMaven {
    name = "org.nibor.autolink_autolink-0.6.0";
    urls = [ "https://repo1.maven.org/maven2/org/nibor/autolink/autolink/0.6.0/autolink-0.6.0.jar" "https://repo1.maven.org/maven2/org/nibor/autolink/autolink/0.6.0/autolink-0.6.0.pom" ];
    hash = "sha256-UyOje39E9ysUXMK3ey2jrm7S6e8EVQboYC46t+B6sdo=";
    installPath = "https/repo1.maven.org/maven2/org/nibor/autolink/autolink/0.6.0";
  };

  "org.openjdk.jmh_jmh-core-1.35" = fetchMaven {
    name = "org.openjdk.jmh_jmh-core-1.35";
    urls = [ "https://repo1.maven.org/maven2/org/openjdk/jmh/jmh-core/1.35/jmh-core-1.35.jar" "https://repo1.maven.org/maven2/org/openjdk/jmh/jmh-core/1.35/jmh-core-1.35.pom" ];
    hash = "sha256-x/U3O9iVa9maPYkYpxqCpn0KysMgU3liJhUwnfgRLb8=";
    installPath = "https/repo1.maven.org/maven2/org/openjdk/jmh/jmh-core/1.35";
  };

  "org.openjdk.jmh_jmh-parent-1.35" = fetchMaven {
    name = "org.openjdk.jmh_jmh-parent-1.35";
    urls = [ "https://repo1.maven.org/maven2/org/openjdk/jmh/jmh-parent/1.35/jmh-parent-1.35.pom" ];
    hash = "sha256-IQnIt0jWZjNk1M7ea1vYvyZ4A+KYuxGR0od7Rvl+Su0=";
    installPath = "https/repo1.maven.org/maven2/org/openjdk/jmh/jmh-parent/1.35";
  };

  "org.ow2.asm_asm-9.8" = fetchMaven {
    name = "org.ow2.asm_asm-9.8";
    urls = [ "https://repo1.maven.org/maven2/org/ow2/asm/asm/9.8/asm-9.8.jar" "https://repo1.maven.org/maven2/org/ow2/asm/asm/9.8/asm-9.8.pom" ];
    hash = "sha256-+veD/6/fvI/ohZYhYhoChm0qeS7TaclJO9qnsSkBUxY=";
    installPath = "https/repo1.maven.org/maven2/org/ow2/asm/asm/9.8";
  };

  "org.ow2.asm_asm-tree-9.8" = fetchMaven {
    name = "org.ow2.asm_asm-tree-9.8";
    urls = [ "https://repo1.maven.org/maven2/org/ow2/asm/asm-tree/9.8/asm-tree-9.8.jar" "https://repo1.maven.org/maven2/org/ow2/asm/asm-tree/9.8/asm-tree-9.8.pom" ];
    hash = "sha256-ZxdFTSgXy5f+gdS/FvxW+0oyf+5+RFUm3hv7G0akkQk=";
    installPath = "https/repo1.maven.org/maven2/org/ow2/asm/asm-tree/9.8";
  };

  "org.scala-lang.modules_scala-asm-9.7.0-scala-2" = fetchMaven {
    name = "org.scala-lang.modules_scala-asm-9.7.0-scala-2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-asm/9.7.0-scala-2/scala-asm-9.7.0-scala-2.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-asm/9.7.0-scala-2/scala-asm-9.7.0-scala-2.pom" ];
    hash = "sha256-yazixBmwEaFEABrjyNXbIEXxfdreoZW8T3NmFFM7sns=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-asm/9.7.0-scala-2";
  };

  "org.scala-lang.modules_scala-asm-9.8.0-scala-1" = fetchMaven {
    name = "org.scala-lang.modules_scala-asm-9.8.0-scala-1";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-asm/9.8.0-scala-1/scala-asm-9.8.0-scala-1.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-asm/9.8.0-scala-1/scala-asm-9.8.0-scala-1.pom" ];
    hash = "sha256-kS1WgHhTdFwkLcqw9gowkcHYWgIgypRv7NR7Fpp7VeY=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-asm/9.8.0-scala-1";
  };

  "org.scala-lang.modules_scala-collection-compat_2.13-2.11.0" = fetchMaven {
    name = "org.scala-lang.modules_scala-collection-compat_2.13-2.11.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_2.13/2.11.0/scala-collection-compat_2.13-2.11.0.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_2.13/2.11.0/scala-collection-compat_2.13-2.11.0.pom" ];
    hash = "sha256-++tF6j10SwWogS7WQJHMqj7uSzo7UVjub4dDQPdogPw=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_2.13/2.11.0";
  };

  "org.scala-lang.modules_scala-collection-compat_2.13-2.13.0" = fetchMaven {
    name = "org.scala-lang.modules_scala-collection-compat_2.13-2.13.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_2.13/2.13.0/scala-collection-compat_2.13-2.13.0.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_2.13/2.13.0/scala-collection-compat_2.13-2.13.0.pom" ];
    hash = "sha256-aQ+I3JuE8U5GIdb4SlHbZWdPu4E/qRIoZSGMMP3g5GE=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_2.13/2.13.0";
  };

  "org.scala-lang.modules_scala-collection-compat_3-2.12.0" = fetchMaven {
    name = "org.scala-lang.modules_scala-collection-compat_3-2.12.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_3/2.12.0/scala-collection-compat_3-2.12.0.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_3/2.12.0/scala-collection-compat_3-2.12.0.pom" ];
    hash = "sha256-ne2PoJ4ge4ygNIDFAkpo++XaJNsiGE7gqtT7HbG4gVs=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-collection-compat_3/2.12.0";
  };

  "org.scala-lang.modules_scala-parallel-collections_2.13-0.2.0" = fetchMaven {
    name = "org.scala-lang.modules_scala-parallel-collections_2.13-0.2.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-parallel-collections_2.13/0.2.0/scala-parallel-collections_2.13-0.2.0.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-parallel-collections_2.13/0.2.0/scala-parallel-collections_2.13-0.2.0.pom" ];
    hash = "sha256-chqRhtzyMJjeR4ohA5YhNjGV8kLHTy5yZjNCyYIO/wo=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-parallel-collections_2.13/0.2.0";
  };

  "org.scala-lang.modules_scala-parser-combinators_2.13-1.1.2" = fetchMaven {
    name = "org.scala-lang.modules_scala-parser-combinators_2.13-1.1.2";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-parser-combinators_2.13/1.1.2/scala-parser-combinators_2.13-1.1.2.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-parser-combinators_2.13/1.1.2/scala-parser-combinators_2.13-1.1.2.pom" ];
    hash = "sha256-sM5GWZ8/K1Jchj4V3FTvaWhfSJiHq0PKtQpd5W94Hps=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-parser-combinators_2.13/1.1.2";
  };

  "org.scala-lang.modules_scala-xml_2.13-2.3.0" = fetchMaven {
    name = "org.scala-lang.modules_scala-xml_2.13-2.3.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_2.13/2.3.0/scala-xml_2.13-2.3.0.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_2.13/2.3.0/scala-xml_2.13-2.3.0.pom" ];
    hash = "sha256-TZaDZ9UjQB20IMvxqxub63LbqSNDMAhFDRtYfvbzI58=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_2.13/2.3.0";
  };

  "org.scala-lang.modules_scala-xml_3-2.3.0" = fetchMaven {
    name = "org.scala-lang.modules_scala-xml_3-2.3.0";
    urls = [ "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_3/2.3.0/scala-xml_3-2.3.0.jar" "https://repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_3/2.3.0/scala-xml_3-2.3.0.pom" ];
    hash = "sha256-Apz2oPaBRFZxl0OqKIKRv7HdAkilk7gFjirguXk5oSI=";
    installPath = "https/repo1.maven.org/maven2/org/scala-lang/modules/scala-xml_3/2.3.0";
  };

  "org.scala-sbt.jline_jline-2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18" = fetchMaven {
    name = "org.scala-sbt.jline_jline-2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18";
    urls = [ "https://repo1.maven.org/maven2/org/scala-sbt/jline/jline/2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18/jline-2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18.jar" "https://repo1.maven.org/maven2/org/scala-sbt/jline/jline/2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18/jline-2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18.pom" ];
    hash = "sha256-1Nq7/UMXSlaZ7iwR1WMryltAmS8/fRCK6u93cm+1uh4=";
    installPath = "https/repo1.maven.org/maven2/org/scala-sbt/jline/jline/2.14.7-sbt-9a88bc413e2b34a4580c001c654d1a7f4f65bf18";
  };

  "org.sonatype.oss_oss-parent-7" = fetchMaven {
    name = "org.sonatype.oss_oss-parent-7";
    urls = [ "https://repo1.maven.org/maven2/org/sonatype/oss/oss-parent/7/oss-parent-7.pom" ];
    hash = "sha256-HDM4YUA2cNuWnhH7wHWZfxzLMdIr2AT36B3zuJFrXbE=";
    installPath = "https/repo1.maven.org/maven2/org/sonatype/oss/oss-parent/7";
  };

  "org.sonatype.oss_oss-parent-9" = fetchMaven {
    name = "org.sonatype.oss_oss-parent-9";
    urls = [ "https://repo1.maven.org/maven2/org/sonatype/oss/oss-parent/9/oss-parent-9.pom" ];
    hash = "sha256-kJ3QfnDTAvamYaHQowpAKW1gPDFDXbiP2lNPzNllIWY=";
    installPath = "https/repo1.maven.org/maven2/org/sonatype/oss/oss-parent/9";
  };

  "org.virtuslab.scala-cli_config_2.13-1.1.3" = fetchMaven {
    name = "org.virtuslab.scala-cli_config_2.13-1.1.3";
    urls = [ "https://repo1.maven.org/maven2/org/virtuslab/scala-cli/config_2.13/1.1.3/config_2.13-1.1.3.jar" "https://repo1.maven.org/maven2/org/virtuslab/scala-cli/config_2.13/1.1.3/config_2.13-1.1.3.pom" ];
    hash = "sha256-VEMBbFMIYxb4azu232W7xSXXnYk6P7eKOKbA7ZgnTTA=";
    installPath = "https/repo1.maven.org/maven2/org/virtuslab/scala-cli/config_2.13/1.1.3";
  };

  "org.virtuslab.scala-cli_specification-level_2.13-1.1.3" = fetchMaven {
    name = "org.virtuslab.scala-cli_specification-level_2.13-1.1.3";
    urls = [ "https://repo1.maven.org/maven2/org/virtuslab/scala-cli/specification-level_2.13/1.1.3/specification-level_2.13-1.1.3.jar" "https://repo1.maven.org/maven2/org/virtuslab/scala-cli/specification-level_2.13/1.1.3/specification-level_2.13-1.1.3.pom" ];
    hash = "sha256-G/6ffz3UFp2Bj/SV9NLIrrq8nzawFZ7qwemXIx+dn8k=";
    installPath = "https/repo1.maven.org/maven2/org/virtuslab/scala-cli/specification-level_2.13/1.1.3";
  };

  "ua.co.k_strftime4j-1.0.5" = fetchMaven {
    name = "ua.co.k_strftime4j-1.0.5";
    urls = [ "https://repo1.maven.org/maven2/ua/co/k/strftime4j/1.0.5/strftime4j-1.0.5.jar" "https://repo1.maven.org/maven2/ua/co/k/strftime4j/1.0.5/strftime4j-1.0.5.pom" ];
    hash = "sha256-Wrg3ftbV/dCtAhULZcti/FJ2XVbpqd9fM4Z6A/fOwAo=";
    installPath = "https/repo1.maven.org/maven2/ua/co/k/strftime4j/1.0.5";
  };

  "com.fasterxml.jackson.core_jackson-annotations-2.12.1" = fetchMaven {
    name = "com.fasterxml.jackson.core_jackson-annotations-2.12.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.12.1/jackson-annotations-2.12.1.pom" ];
    hash = "sha256-anUbI5JS/lVsxPul1sdmtNFsJbiyHvyz9au/cBV0L6w=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.12.1";
  };

  "com.fasterxml.jackson.core_jackson-annotations-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson.core_jackson-annotations-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.15.1/jackson-annotations-2.15.1.jar" "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.15.1/jackson-annotations-2.15.1.pom" ];
    hash = "sha256-hwI7CChHkZif7MNeHDjPf6OuNcncc9i7zIET6JUiSY8=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.15.1";
  };

  "com.fasterxml.jackson.core_jackson-core-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson.core_jackson-core-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-core/2.15.1/jackson-core-2.15.1.jar" "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-core/2.15.1/jackson-core-2.15.1.pom" ];
    hash = "sha256-07N9Rg8OKF7hTLa+0AoF1hImT3acHpQBIJhHBnLUSOs=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-core/2.15.1";
  };

  "com.fasterxml.jackson.core_jackson-databind-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson.core_jackson-databind-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-databind/2.15.1/jackson-databind-2.15.1.jar" "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-databind/2.15.1/jackson-databind-2.15.1.pom" ];
    hash = "sha256-t8Sge4HbKg8XsqNgW69/3G3RKgK09MSCsPH7XYtsrew=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-databind/2.15.1";
  };

  "com.fasterxml.jackson.dataformat_jackson-dataformat-yaml-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson.dataformat_jackson-dataformat-yaml-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/dataformat/jackson-dataformat-yaml/2.15.1/jackson-dataformat-yaml-2.15.1.jar" "https://repo1.maven.org/maven2/com/fasterxml/jackson/dataformat/jackson-dataformat-yaml/2.15.1/jackson-dataformat-yaml-2.15.1.pom" ];
    hash = "sha256-gSpEZqpCXmFGg86xQeOlNRNdyBmiM/rN2kCTGhjhHt4=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/dataformat/jackson-dataformat-yaml/2.15.1";
  };

  "com.fasterxml.jackson.dataformat_jackson-dataformats-text-2.15.1" = fetchMaven {
    name = "com.fasterxml.jackson.dataformat_jackson-dataformats-text-2.15.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/dataformat/jackson-dataformats-text/2.15.1/jackson-dataformats-text-2.15.1.pom" ];
    hash = "sha256-1RiIP6cIRZoOMBV2+vmJJOYXMarqg+4l7XQ8S7OvAvg=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/dataformat/jackson-dataformats-text/2.15.1";
  };

  "com.fasterxml.jackson.datatype_jackson-datatype-jsr310-2.12.1" = fetchMaven {
    name = "com.fasterxml.jackson.datatype_jackson-datatype-jsr310-2.12.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/datatype/jackson-datatype-jsr310/2.12.1/jackson-datatype-jsr310-2.12.1.jar" "https://repo1.maven.org/maven2/com/fasterxml/jackson/datatype/jackson-datatype-jsr310/2.12.1/jackson-datatype-jsr310-2.12.1.pom" ];
    hash = "sha256-YH7YMZY1aeamRA6aVvF2JG3C1YLZhvaMpVCegAfdhFU=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/datatype/jackson-datatype-jsr310/2.12.1";
  };

  "com.fasterxml.jackson.module_jackson-modules-java8-2.12.1" = fetchMaven {
    name = "com.fasterxml.jackson.module_jackson-modules-java8-2.12.1";
    urls = [ "https://repo1.maven.org/maven2/com/fasterxml/jackson/module/jackson-modules-java8/2.12.1/jackson-modules-java8-2.12.1.pom" ];
    hash = "sha256-x5YmdPGcWOpCompDhApY6o5VZ+IUVHTbeday5HVW/NQ=";
    installPath = "https/repo1.maven.org/maven2/com/fasterxml/jackson/module/jackson-modules-java8/2.12.1";
  };

  "com.github.plokhotnyuk.jsoniter-scala_jsoniter-scala-core_2.13-2.13.39" = fetchMaven {
    name = "com.github.plokhotnyuk.jsoniter-scala_jsoniter-scala-core_2.13-2.13.39";
    urls = [ "https://repo1.maven.org/maven2/com/github/plokhotnyuk/jsoniter-scala/jsoniter-scala-core_2.13/2.13.39/jsoniter-scala-core_2.13-2.13.39.jar" "https://repo1.maven.org/maven2/com/github/plokhotnyuk/jsoniter-scala/jsoniter-scala-core_2.13/2.13.39/jsoniter-scala-core_2.13-2.13.39.pom" ];
    hash = "sha256-DXtXlBoBOSHHqlmZp9SwZ/JMsU5X9AKyI2Ug7ZwoPJ4=";
    installPath = "https/repo1.maven.org/maven2/com/github/plokhotnyuk/jsoniter-scala/jsoniter-scala-core_2.13/2.13.39";
  };

  "com.google.code.findbugs_jsr305-3.0.2" = fetchMaven {
    name = "com.google.code.findbugs_jsr305-3.0.2";
    urls = [ "https://repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2/jsr305-3.0.2.jar" "https://repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2/jsr305-3.0.2.pom" ];
    hash = "sha256-eq7d9gzPBemWTgv/S9uUEKh7A2rqnKOhK0L4/e6N3/s=";
    installPath = "https/repo1.maven.org/maven2/com/google/code/findbugs/jsr305/3.0.2";
  };

  "com.google.code.gson_gson-2.10.1" = fetchMaven {
    name = "com.google.code.gson_gson-2.10.1";
    urls = [ "https://repo1.maven.org/maven2/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar" "https://repo1.maven.org/maven2/com/google/code/gson/gson/2.10.1/gson-2.10.1.pom" ];
    hash = "sha256-i+rvjAxrIQEGvGfKhfyuaxlQyGLIYLcATflf5jO59og=";
    installPath = "https/repo1.maven.org/maven2/com/google/code/gson/gson/2.10.1";
  };

  "com.google.code.gson_gson-parent-2.10.1" = fetchMaven {
    name = "com.google.code.gson_gson-parent-2.10.1";
    urls = [ "https://repo1.maven.org/maven2/com/google/code/gson/gson-parent/2.10.1/gson-parent-2.10.1.pom" ];
    hash = "sha256-ziwFqeFqWmM5vUPJYof+P7cXBkQ9L/6JdR+DfJmxyoI=";
    installPath = "https/repo1.maven.org/maven2/com/google/code/gson/gson-parent/2.10.1";
  };

  "io.github.alexarchambault.native-terminal_native-terminal-no-ffm-0.0.9.1" = fetchMaven {
    name = "io.github.alexarchambault.native-terminal_native-terminal-no-ffm-0.0.9.1";
    urls = [ "https://repo1.maven.org/maven2/io/github/alexarchambault/native-terminal/native-terminal-no-ffm/0.0.9.1/native-terminal-no-ffm-0.0.9.1.jar" "https://repo1.maven.org/maven2/io/github/alexarchambault/native-terminal/native-terminal-no-ffm/0.0.9.1/native-terminal-no-ffm-0.0.9.1.pom" ];
    hash = "sha256-fHtvFUaVlrgdz+S3mPlxXjA4mpSBWC+hjW3U7h5NFo0=";
    installPath = "https/repo1.maven.org/maven2/io/github/alexarchambault/native-terminal/native-terminal-no-ffm/0.0.9.1";
  };

  "io.github.alexarchambault.windows-ansi_windows-ansi-0.0.6" = fetchMaven {
    name = "io.github.alexarchambault.windows-ansi_windows-ansi-0.0.6";
    urls = [ "https://repo1.maven.org/maven2/io/github/alexarchambault/windows-ansi/windows-ansi/0.0.6/windows-ansi-0.0.6.jar" "https://repo1.maven.org/maven2/io/github/alexarchambault/windows-ansi/windows-ansi/0.0.6/windows-ansi-0.0.6.pom" ];
    hash = "sha256-TGUrDCPYFiXV5b2If3u4KviH3JxZttMOKL1HUHqIWRo=";
    installPath = "https/repo1.maven.org/maven2/io/github/alexarchambault/windows-ansi/windows-ansi/0.0.6";
  };

  "net.java.dev.jna_jna-5.13.0" = fetchMaven {
    name = "net.java.dev.jna_jna-5.13.0";
    urls = [ "https://repo1.maven.org/maven2/net/java/dev/jna/jna/5.13.0/jna-5.13.0.jar" "https://repo1.maven.org/maven2/net/java/dev/jna/jna/5.13.0/jna-5.13.0.pom" ];
    hash = "sha256-LP1W3fVxMEP6po1dlkAseu3pSeSnobemZJaxKivwqDs=";
    installPath = "https/repo1.maven.org/maven2/net/java/dev/jna/jna/5.13.0";
  };

  "net.java.dev.jna_jna-5.15.0" = fetchMaven {
    name = "net.java.dev.jna_jna-5.15.0";
    urls = [ "https://repo1.maven.org/maven2/net/java/dev/jna/jna/5.15.0/jna-5.15.0.jar" "https://repo1.maven.org/maven2/net/java/dev/jna/jna/5.15.0/jna-5.15.0.pom" ];
    hash = "sha256-7iRfZecKpdVWwZgDlGA+w6bI461J7TB+lr8I5sWiaoY=";
    installPath = "https/repo1.maven.org/maven2/net/java/dev/jna/jna/5.15.0";
  };

  "net.java.dev.jna_jna-5.17.0" = fetchMaven {
    name = "net.java.dev.jna_jna-5.17.0";
    urls = [ "https://repo1.maven.org/maven2/net/java/dev/jna/jna/5.17.0/jna-5.17.0.jar" "https://repo1.maven.org/maven2/net/java/dev/jna/jna/5.17.0/jna-5.17.0.pom" ];
    hash = "sha256-q4PFCy/O+i1lIiNaf627UILQWmnOgIZTGeMzu5N3M+Q=";
    installPath = "https/repo1.maven.org/maven2/net/java/dev/jna/jna/5.17.0";
  };

  "org.apache.geronimo.genesis_genesis-2.0" = fetchMaven {
    name = "org.apache.geronimo.genesis_genesis-2.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/geronimo/genesis/genesis/2.0/genesis-2.0.pom" ];
    hash = "sha256-lcX5R64+07kRLqpdfkay87hJI6ykVn/wUXs142Elips=";
    installPath = "https/repo1.maven.org/maven2/org/apache/geronimo/genesis/genesis/2.0";
  };

  "org.apache.geronimo.genesis_genesis-default-flava-2.0" = fetchMaven {
    name = "org.apache.geronimo.genesis_genesis-default-flava-2.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/geronimo/genesis/genesis-default-flava/2.0/genesis-default-flava-2.0.pom" ];
    hash = "sha256-jkGo9ePZSnxqcIOQIuAz1ZTPNjjx2vc01oxtt6EJuUk=";
    installPath = "https/repo1.maven.org/maven2/org/apache/geronimo/genesis/genesis-default-flava/2.0";
  };

  "org.apache.geronimo.genesis_genesis-java5-flava-2.0" = fetchMaven {
    name = "org.apache.geronimo.genesis_genesis-java5-flava-2.0";
    urls = [ "https://repo1.maven.org/maven2/org/apache/geronimo/genesis/genesis-java5-flava/2.0/genesis-java5-flava-2.0.pom" ];
    hash = "sha256-CTKaQ0fTVeVBnQrWm4TCcbTONXm/N6bPXPGXx0hToLQ=";
    installPath = "https/repo1.maven.org/maven2/org/apache/geronimo/genesis/genesis-java5-flava/2.0";
  };

  "org.apache.logging.log4j_log4j-2.24.3" = fetchMaven {
    name = "org.apache.logging.log4j_log4j-2.24.3";
    urls = [ "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j/2.24.3/log4j-2.24.3.pom" ];
    hash = "sha256-bWuk6kxsiWW675JezWblZ8RdkKFg9C/3CgzdMGJr1Z8=";
    installPath = "https/repo1.maven.org/maven2/org/apache/logging/log4j/log4j/2.24.3";
  };

  "org.apache.logging.log4j_log4j-api-2.24.3" = fetchMaven {
    name = "org.apache.logging.log4j_log4j-api-2.24.3";
    urls = [ "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-api/2.24.3/log4j-api-2.24.3.jar" "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-api/2.24.3/log4j-api-2.24.3.pom" ];
    hash = "sha256-y6wgpqMFwL3B3CrUbTI4HQTBjc4YSWxn0WF8QQSjpFw=";
    installPath = "https/repo1.maven.org/maven2/org/apache/logging/log4j/log4j-api/2.24.3";
  };

  "org.apache.logging.log4j_log4j-bom-2.24.3" = fetchMaven {
    name = "org.apache.logging.log4j_log4j-bom-2.24.3";
    urls = [ "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-bom/2.24.3/log4j-bom-2.24.3.pom" ];
    hash = "sha256-UNEo/UyoskA/8X62/rwMQObDQxfHDiJKj2pBP9SNoek=";
    installPath = "https/repo1.maven.org/maven2/org/apache/logging/log4j/log4j-bom/2.24.3";
  };

  "org.apache.logging.log4j_log4j-core-2.24.3" = fetchMaven {
    name = "org.apache.logging.log4j_log4j-core-2.24.3";
    urls = [ "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-core/2.24.3/log4j-core-2.24.3.jar" "https://repo1.maven.org/maven2/org/apache/logging/log4j/log4j-core/2.24.3/log4j-core-2.24.3.pom" ];
    hash = "sha256-kRXpkDJtXT0VoEyxj5hIc8Z8foh8rKnFqCpjohdh5LQ=";
    installPath = "https/repo1.maven.org/maven2/org/apache/logging/log4j/log4j-core/2.24.3";
  };

}
# Project Source Hash:sha256-EKtgGu27yWn+bqzikhtRRv2CnqZL3g+fK4Gx+UZw2Xc=
