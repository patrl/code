# Makefile for a `md` > `pdf` (via `tex`) workflow

A Makefile for compiling Markdown markup to `pdf`. Uses `pandoc` to convert
all the `md` files in a directory to standalone `tex` files, then uses
`latexmk` to compile those `tex` files to `pdf`.

For many use cases, this is much faster than `pandoc` alone: `latexmk`
generates helper files that help speed along non-initial compilations, and
(unlike `pandoc`) only re-compiles as many times as needed to get
cross-references and citations right. Using `latexmk` also makes it possible
in principle to externalize your `tikz` diagrams.

## Usage

Place `Makefile` in a directory with your `md` file(s). Then, navigate to that
directory with Terminal (or whatever). The following commands are available:

```
$ make              # Do a basic compilation, using pandoc's latex writer (and
                    # your default.latex template).
```

```
$ make watch        # Watch md files for changes and recompile if needed. Use
                    # control-c to break out.
```

```
$ make clean        # Get rid of everything but the md and pdf files.
```

```
$ [cmd] OUT=beamer  # Generate slides, using pandoc's beamer writer (and your
                    # default.beamer template), for [cmd] in {make, make watch}.
```

## Dependencies

You'll need `pandoc` and `latexmk`.

If you don't plan on invoking `make watch`, it should work out of the box. If
you want to `make watch`, you'll need
[`fswatch`](https://github.com/emcrisostomo/fswatch), which you can install
with [Homebrew](http://brew.sh/) (`brew install fswatch`) or
[MacPorts](https://www.macports.org/) (`port install fswatch`). You'll need OS
X to use `fswatch`.

## Notes

The `aux` files for `latex` and `beamer` can step on each other's toes. If
you're getting strange errors and/or output, try running `make clean`.
