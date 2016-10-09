# orn

*orn* is the swiss-army knife for shell scripting. It aims to replace
`make` and also be a general purpose shell-scripting language.

*orn* is designed to have a very small footprint (smaller than `bash`)
and fast (faster than `bash` too), with negligible tear-down time.
It is type-safe and the interpreter is implemented in a type-safe
and memory-safe language too (Rust!).
It also provides modern programming language primitives instead of
the nightmare that `bash` is.

### Currently implemented

* functions
* mutable and immutable variables
* `uint`, `int`, `float`, `str`, and `bool` data types
* functions are first class! they automatically get the `fn` type
* closures work as expected
* if/else/else if
* everything is an expression except variable bindings
* all blocks (including ifs and functions) automatically return
  the value of the last evaluated expressions
* an `echo` function monkey patched in the vm callsite to print to
  stdout. (See TODO)
* full stack trace visible on errors with location in source
* parse time errors are printed with location and friendly error
  messages too!
* usual stuff like equality operators, arithmetic operators etc.
  however binary expressions are currently passed straight-way
  left-to-right without any precedence check (see TODO)

Example orn code demonstrating a couple of these things and the syntax:

```
let x = 1; # immutable binding. type inferred as uint
let mut y = -2.0; # mutable binding. type inferred as float

fn subtract_1(z) {
	if true {
		x + y + z # cascaded auto return
	}
}

echo(subtract_1(55)) # prints 54
```

### Usage

*orn* is written in Rust. As such, it is distributed as a single binary
which you can drop in your `$PATH` and start writing shell scripts. To run
them, just pass the path to your script as the first argument to `orn`.
Alternatively, you could use shebangs and mark your scripts as executables.

To compile the *orn* interpreter yourself, you need cargo. Clone the
source code and run `cargo build --release`, and copy `target/release/orn`.
To build a dynamically linked binary, you can use this:

```
cargo rustc --release --bin orn -- -C prefer-dynamic
```

### TODO

* precedence based parsing for binary expressions
* type-checker
* namespaced standard library (`path` and `io` modules for a start)
* homogenous arrays
* nullable type
* dict type
* embedding API
* documentation
* `make` like recipes with pattern matching on shell args (high priority)
* allow calling *orn* as a global binary and pick orn code from the first
  *ornfile* in the calling directory or one of its parents (like git's
  traversal to find `.git` directory). rename the interpreter itself to
  something else and symlink it to `orn` on installation to allow the binary
  to serve the dual purpose by detecting `$argv[0]` at runtime.

## Author

Awal Garg <awalgarg@gmail.com> ,[@awalGarg](https://twitter.com/awalGarg)

## License

MIT
