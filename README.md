# Build Instructions

First you need to setup jsCoq and related tools:
```
make node_modules    # Install jsCoq and other tools
```

once that is done, you can work with your files as:

```
$ make       # Build Coq files (customize makefile if you need)
$ make serve # Open a web server with the jsCoq files
```

Note that `make serve` doesn't need to be restarted after a regular
`make`.

# Tweaks from official distro

We have customized the following files from the oficial distro:

+ custom load of packages in `jscoq-agent.js`
+ custom paths in `jscoqdoc` binary

We default to the WebAssembly jsCoq version.

You may want to tweak more stuff too.

# TODO:

- tweak CSS?
