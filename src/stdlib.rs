use vm::{ StackFrame, OrnBinding, OrnVal, RuntimeError, RuntimeErrorType, Stack };
use std::collections::HashMap;
use std::rc::Rc;
use std::process::{ Command, Stdio };

macro_rules! expect_argument_type {
    ($iter:expr, $arg:pat, $consequence:block, $failure_msg:expr) => {
        match $iter.next().map(|x| x.as_ref()) {
            Some($arg) => $consequence,
            Some(val) => {
                return Err(RuntimeError {
                    error_type: RuntimeErrorType::TypeError,
                    line: 0,
                    column: 0,
                    msg: format!("Expected {}. Got {}.", stringify!($arg), val),
                });
            },
            None => {
                return Err(RuntimeError {
                    error_type: RuntimeErrorType::TypeError,
                    line: 0,
                    column: 0,
                    msg: format!("Expected {}. Got nothing.", stringify!($arg)),
                });
            },
        }
    }
}

fn array_each(stack: &mut Stack, vec: Vec<Rc<OrnVal>>) -> Result<Rc<OrnVal>, RuntimeError> {
    let arr = match vec.get(0).map(|x| x.as_ref()) {
        Some(&OrnVal::Array { ref values, .. }) => { values },
        _ => {
            return Err(RuntimeError {
                error_type: RuntimeErrorType::TypeError,
                line: 0, 
                column: 0,
                msg: format!("Array.forEach expected an array. Gimme array or gtfo."),
            });
        },
    };
    let callback = match vec.get(1) {
        Some(x) => { x },
        None => {
            return Err(RuntimeError {
                error_type: RuntimeErrorType::TypeError,
                line: 0,
                column: 0,
                msg: format!("Array.forEach expects a function too..."),
            });
        },
    };
    for elem in arr.borrow().iter() {
        match stack.call_user_func(callback.clone(), vec![elem.clone()]) {
            Ok(_) => {},
            e @ Err(_) => { return e; },
        }
    }
    Ok(Rc::new(OrnVal::Bool(false)))
}

fn echo(_: &mut Stack, vec: Vec<Rc<OrnVal>>) -> Result<Rc<OrnVal>, RuntimeError> {
    for arg in vec.iter() {
        println!("{}", arg);
    }
    Ok(Rc::new(OrnVal::Bool(false)))
}

fn exec(_: &mut Stack, vec: Vec<Rc<OrnVal>>) -> Result<Rc<OrnVal>, RuntimeError> {
    let program = expect_argument_type!(vec.iter(), &OrnVal::Str(ref x), { x.to_string() }, "exec takes first argument as string bro");
    let mut cmd = Command::new("sh");
    cmd
        .arg("-c")
        .arg(program)
        .stdout(Stdio::piped());
    let mut p = cmd.spawn().unwrap();
    return Ok(Rc::new(OrnVal::Str(String::from_utf8(p.wait_with_output().unwrap().stdout).unwrap())));
}


macro_rules! add_module {
    ($frame:ident, $name:ident, $( $tag:ident [ $init:expr ] ),*) => {
        let mut proto = HashMap::new();
        $(
            proto.insert(stringify!($tag).to_string(), Rc::new(OrnVal::BuiltIn { identifier: stringify!($tag).to_string(), func: $init }));
        )*
        $frame.scope.insert(
            stringify!($name).to_string(),
            OrnBinding {
                mutable: false,
                val: Rc::new(OrnVal::Mod(proto)),
            },
        );
    }
}

macro_rules! add_builtin {
    ($frame:ident, $name:ident, $init:expr) => {
        $frame.scope.insert(stringify!($name).to_string(), OrnBinding {
            mutable: false,
            val: Rc::new(OrnVal::BuiltIn { identifier: stringify!($name).to_string(), func: $init }),
        });
    }
}

pub fn get_amazing_orn_stdlib_as_stackframe() -> StackFrame {
    let mut frame = StackFrame::new();

    add_module!(
        frame,
        Array,
        each [ array_each ]
    );

    add_module!(
        frame,
        Sh,
        exec [ exec ]
    );

    add_builtin!(
        frame,
        echo,
        echo
    );

    frame
}
