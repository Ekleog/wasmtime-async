# wasmtime-async

This crate is an extension to the
[`wasmtime`](https://github.com/bytecodealliance/wasmtime/blob/master/README.md)
crate. It makes it possible to use wasmtime along with futures,
without having to consider every WebAssembly call as blocking. Note
however that it is designed only for cases where the time spent in
WebAssembly is indeed not enough to warrant running it in a worker
thread -- it is designed with, in mind, relatively lightweight
WebAssembly code that then calls into async callbacks provided from
the rust side.

The WebAssembly code will be run on a specific stack and, when it
calls an async callback provided by rust, will be interrupted until
the future has returned. As such, so long as the time spent inside
WebAssembly is not enough to warrant in itself running the whole task
on a blocking executor, it should be possible to run WebAssembly code
that integrates seamlessly with async code.

The drawback of this approach is that the async callbacks appear as
though they were blocking to WebAssembly. This is unfortunately
necessary to not require the WebAssembly code itself to be
async-ready.

# Usage

This crate provides two main elements:
- The [`Stack`] struct, that owns a stack on which WebAssembly code
  can run
- The [`FuncExt`] trait, that provides extension methods for
  [`wasmtime::Func`] for dealing with asynchronous callbacks provided
  by Rust to WebAssembly.

## [`Stack`]

The [`Stack`] struct is easy to use: just use [`Stack::new`], and it
will create a stack on which WebAssembly code can run.

Running code on a [`Stack`] takes a mutable reference to it so long as
the code is running, thus preventing multiple functions from using the
same stack without any runtime cost or unsafe usage.

## [`FuncExt`]

The [`FuncExt`] provides most of the interesting methods in this crate.

### Wrapping async functions for use from WebAssembly

First, use the methods to wrap async functions in Rust so that they
could be used transparently from WebAssembly:

- [`FuncExt::new_async`], corresponding to [`wasmtime::Func::new`]
- [`FuncExt::wrap_async`], corresponding to [`wasmtime::Func::wrap`]
  with callbacks that do not take a [`wasmtime::Caller`] as first
  argument
- [`FuncExt::wrap_async0`] to [`FuncExt::wrap_async15`], corresponding
  to [`wasmtime::Func::wrap`] with callbacks that do take a
  [`wasmtime::Caller`] as first argument

It would be better to have a single [`FuncExt::wrap_async`] function,
but unfortunately, due to both orphan rules and [a probable limitation
of rustc](https://github.com/rust-lang/rust/issues/71852), it is not
possible to do so at the moment, hence the multiple methods that
handle each part of [`Func::wrap`].

### Calling WebAssembly that uses async functions

When calling into WebAssembly code that potentially uses async
functions, you **must** use an async-ready calling function, or a
WebAssembly panic will arise!

The functions are these:

- [`FuncExt::call_async`], corresponding to [`wasmtime::Func::call`]
- [`FuncExt::get_async`], which returns an [`AsyncGetter`] object. The
  [`AsyncGetter`] object is just here to circumvent limitations in the
  Rust type system, and in particular associated existential types. On
  [`AsyncGetter`], you can call the [`AsyncGetter::get0`] to
  [`AsyncGetter::get15`] functions just like you would have called
  them on [`wasmtime::Func`].
