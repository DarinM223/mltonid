mltonid
=======

Building:
---------

Building with MLton:

```
mlton mltonid.mlb
```

Building with Poly/ML:

```
./build_polyml.sh
polyc build.sml -o mltonid
```

MLton files are required to be in a standard location like `/usr/local/lib/mlton`.

Building with SML/NJ:

```
ml-build mltonid.cm Main.main mltonid
sml @SMLload=mltonid.amd64-linux <args>
```

Where amd64-linux is replaced with your architecture.

Running:
--------

Environment variables expected:

| Required | Variable      | Value |
|----------|---------------|-------|
| Yes      | SML_LIB       | `<mlton_install_dir>/sml` (Example: `/usr/local/lib/mlton/sml`) |
| Yes      | LIB_MLTON_DIR | `<mlton_build_dir>/build/lib/mlton` (Example: `/home/user/mlton/build/lib/mlton`) |
| No       | TARGET        | `self` (default) |