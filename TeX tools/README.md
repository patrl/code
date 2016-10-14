# Makefile for a `md` > `pdf` (via `tex`) workflow

A Makefile for compiling Markdown markup to `pdf`. Uses `pandoc` to convert
Markdown to `tex`, then uses `latexmk` to compile the `tex` to `pdf`.

For many use cases, this is better than `pandoc` alone: `latexmk` generates
helper files (e.g., `aux`'s) that help speed along non-initial compilations.

## Usage

Place `Makefile` in a directory with your `md` file. Then, navigate to that
directory with Terminal (or whatever). The following commands are available:

```
$ make              # Does a basic compilation, using pandoc's latex template
```

```
$ make watch        # Watches the md file for changes and recompiles if needed
                    # Use Control-c to break out
```

```
$ make clean        # Gets rid of everything but the md and pdf files
```

```
$ [cmd] OUT=beamer  # Outputs slides, for any [cmd] in {make, make watch}
```

## Dependencies

If you want to issue `make watch` commands, you'll need
[`fswatch`](https://github.com/emcrisostomo/fswatch), which you can install
with [Homebrew](http://brew.sh/) (`brew install fswatch`) or
[MacPorts](https://www.macports.org/) (`port install fswatch`). You'll need OS
X to use `fswatch`.

If you don't plan on invoking `make watch`, it should work out of the box
(assuming you have `pandoc` and `latexmk`!).

## Notes

The `aux` files for `latex` and `beamer` can step on each other's toes. If
you're getting strange errors and/or output, try running `make clean`.
