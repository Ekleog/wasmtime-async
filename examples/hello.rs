// Copyright 2020 The Wasmtime-Async Developers. See the version
// control history for a full list.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use anyhow::Result;
use wasmtime::{Func, Instance, Module, Store};
use wasmtime_async::prelude::*;

fn main() -> Result<()> {
    // Prepare the environment like for a regular wasmtime program
    let store = Store::default();
    let module = Module::from_file(&store, "examples/hello.wat")?;

    // To wrap async functions, use `wrap_async`
    let hello_func = Func::wrap_async(&store, || async {
        smol::blocking!(println!("Hello World!"));
    });

    // Continue things like you normally would for a regular wasmtime
    // program
    let imports = [hello_func.into()];
    let instance = Instance::new(&module, &imports)?;

    // But, when extracting the function, use `.get_async()` to get an
    // async-ready version of it
    let run = instance
        .get_func("run")
        .ok_or(anyhow::format_err!("failed to find `run` function export"))?
        .get_async()
        .get0::<()>()?;

    smol::run(async {
        // When you want to run the future, you must provide a stack
        // to run it
        let mut stack = wasmtime_async::Stack::new(16 * 1024)?;
        run(&mut stack).await?;

        // And then, if you want to run another future (or the same),
        // you can reuse a stack, provided that the previous future
        // running on it has finished executing (which is enforced by
        // the `&mut` borrow)
        run(&mut stack).await?;

        Ok::<_, anyhow::Error>(())
    })?;

    Ok(())
}
