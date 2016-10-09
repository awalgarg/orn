use parser::{ Statement, Expression, ExpressionSource, Block, BinaryOperator, UnaryOperator, FunctionParameter, DataType };
use std::rc::Rc;
use std::cell::Ref;
use std::cell::RefCell;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt;
use std::cmp::Ordering;
use std::ops::{ Sub, Mul, Div, Rem };

pub struct OrnBinding {
    mutable: bool,
    val: Rc<OrnVal>,
}

pub enum OrnVal {
    Fn {
        identifier: String,
        params: Vec<FunctionParameter>,
        return_type: DataType,
        body: Block,
        env: Vec<Rc<RefCell<StackFrame>>>,
        line: u32,
        column: u32,
    },
    Str(String),
    UInt(u32),
    Int(i32),
    Float(f64),
    Bool(bool),
}

impl fmt::Display for OrnVal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &OrnVal::Fn { ref identifier, ref params, ref return_type, .. } => {
                write!(
                    f,
                    "fn {} ({}) -> {}",
                    identifier,
                    params.iter().map(|param| param.to_string()).collect::<Vec<_>>().join(", "),
                    return_type
                )
            },
            &OrnVal::Str(ref s) => {
                write!(f, "\"{}\"", s)
            },
            &OrnVal::UInt(u) => {
                write!(f, "{}", u)
            },
            &OrnVal::Int(i) => {
                write!(f, "{}", i)
            },
            &OrnVal::Float(fl) => {
                write!(f, "{}", fl)
            },
            &OrnVal::Bool(b) => {
                write!(f, "{}", b)
            },
        }
    }
}

pub struct StackFrame {
    scope: HashMap<String, OrnBinding>,
}

pub struct Stack {
    pub frames: Vec<Rc<RefCell<StackFrame>>>,
    pub call_stack: Vec<(u32, u32, String)>,
}

pub enum RuntimeErrorType {
    ReferenceError,
    TypeError,
    InitializationError,
}

impl fmt::Display for RuntimeErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &RuntimeErrorType::ReferenceError => {
                write!(f, "ReferenceError")
            },
            &RuntimeErrorType::TypeError => {
                write!(f, "TypeError")
            },
            &RuntimeErrorType::InitializationError => {
                write!(f, "InitializationError")
            },
        }
    }
}

pub struct RuntimeError {
    pub error_type: RuntimeErrorType,
    pub msg: String,
    pub line: u32,
    pub column: u32,
}

type ErrorStack = Vec<RuntimeError>;

macro_rules! operate_on_numbers_magically {
    ($x:expr, $y:expr, $op:expr, $line:expr, $column:expr) => {
        match ($x, $y) {
            (&OrnVal::UInt(ref x), &OrnVal::UInt(ref y)) => {
                Ok(Rc::new(OrnVal::UInt($op(x, y))))
            },
            (&OrnVal::UInt(ref x), &OrnVal::Float(ref y)) => {
                Ok(Rc::new(OrnVal::Float($op(*x as f64, y))))
            },
            (&OrnVal::UInt(ref x), &OrnVal::Int(ref y)) => {
                Ok(Rc::new(OrnVal::Int($op(*x as i32, y))))
            },
            (&OrnVal::Int(ref x), &OrnVal::Int(ref y)) => {
                Ok(Rc::new(OrnVal::Int($op(x, y))))
            },
            (&OrnVal::Int(ref x), &OrnVal::Float(ref y)) => {
                Ok(Rc::new(OrnVal::Float($op(*x as f64, y))))
            },
            (&OrnVal::Int(ref x), &OrnVal::UInt(ref y)) => {
                Ok(Rc::new(OrnVal::Int($op(x, *y as i32))))
            },
            (&OrnVal::Float(ref x), &OrnVal::Float(ref y)) => {
                Ok(Rc::new(OrnVal::Float($op(x, y))))
            },
            (&OrnVal::Float(ref x), &OrnVal::UInt(ref y)) => {
                Ok(Rc::new(OrnVal::Float($op(x, *y as f64))))
            },
            (&OrnVal::Float(ref x), &OrnVal::Int(ref y)) => {
                Ok(Rc::new(OrnVal::Float($op(x, *y as f64))))
            },
            (ref x, ref y) => {
                return Err(RuntimeError {
                    error_type: RuntimeErrorType::TypeError,
                    line: $line,
                    column: $column,
                    msg: format!("Cannot use operator {} on {} and {}. Perhaps try JavaScript instead? :)", stringify!($op), x, y),
                });
            },
        }
    }
}

macro_rules! compare_numbers_magically {
    ($x:expr, $y:expr, $op:expr, $line:expr, $column:expr) => {
        match ($x, $y) {
            (&OrnVal::UInt(ref x), &OrnVal::UInt(ref y)) => { $op(x, y) },
            (&OrnVal::UInt(ref x), &OrnVal::Float(ref y)) => { $op(&(*x as f64), y) },
            (&OrnVal::UInt(ref x), &OrnVal::Int(ref y)) => { $op(&(*x as i32), y) },
            (&OrnVal::Int(ref x), &OrnVal::Int(ref y)) => { $op(x, y) },
            (&OrnVal::Int(ref x), &OrnVal::Float(ref y)) => { $op(&(*x as f64), y) },
            (&OrnVal::Int(ref x), &OrnVal::UInt(ref y)) => { $op(x, &(*y as i32)) },
            (&OrnVal::Float(ref x), &OrnVal::Float(ref y)) => { $op(x, y) },
            (&OrnVal::Float(ref x), &OrnVal::UInt(ref y)) => { $op(x, &(*y as f64)) },
            (&OrnVal::Float(ref x), &OrnVal::Int(ref y)) => { $op(x, &(*y as f64)) },
            (ref x, ref y) => {
                return Err(RuntimeError {
                    error_type: RuntimeErrorType::TypeError,
                    line: $line,
                    column: $column,
                    msg: format!("Cannot use operator {} on {} and {}. Perhaps try JavaScript instead? :)", stringify!($op), x, y),
                });
            },
        }
    }
}

impl StackFrame {
    pub fn new() -> StackFrame {
        StackFrame { scope: HashMap::new() }
    }
}

impl Stack {
    pub fn new() -> Stack {
        Stack { frames: vec![Rc::new(RefCell::new(StackFrame::new()))], call_stack: Vec::new() }
    }
    fn add_binding(&mut self, id: &str, mutable: bool, val: Rc<OrnVal>) {
        self
            .frames
            .last()
            .expect("getting last frame while adding binding")
            .borrow_mut()
            .scope
            .insert(id.to_string(), OrnBinding { mutable: mutable, val: val });
    }
    fn get_value(&self, id: &str) -> Option<Rc<OrnVal>> {
        for frame_ref in self.frames.iter().rev() {
            let frame: Ref<StackFrame> = frame_ref.as_ref().borrow();
            match frame.scope.get(id) {
                Some(ref binding) => { return Some(binding.val.clone()); },
                None => { continue; },
            }
        }
        None
    }
    pub fn eval_stmt(&mut self, stmt: &Statement) -> Result<Rc<OrnVal>, RuntimeError> {
        match (*stmt).clone() {
            Statement::ExpressionStatement(expr_source) => {
                let line = expr_source.line;
                let column = expr_source.column;
                match expr_source.expr {
                    Expression::Fn { identifier, params, return_type, body } => {
                        let mut frame = self
                                            .frames
                                            .last()
                                            .expect("getting last frame while parsing fn expression statement")
                                            .as_ref()
                                            .borrow_mut();
                        match frame.scope.get(&identifier) {
                            Some(_) => {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::InitializationError,
                                    line: line,
                                    column: column,
                                    msg: format!("There is already a binding by the name \"{}\" in scope. Pick another name?", identifier),
                                });
                            },
                            None => {
                                let val = Rc::new(OrnVal::Fn {
                                    identifier: identifier.clone(),
                                    params: params,
                                    return_type: return_type,
                                    body: body,
                                    line: line,
                                    column: column,
                                    env: self.frames.iter().map(|x| x.clone()).collect::<Vec<_>>(),
                                });
                                frame.scope.insert(identifier, OrnBinding { mutable: false, val: val.clone() });
                                return Ok(val);
                            },
                        }
                    },
                    _ => {
                        self.eval_expr(&expr_source)
                    },
                }
            },
            Statement::Let { mutable, identifier, data_type, initializer } => {
                let val = try!(self.eval_expr(&initializer));
                // note that we don't do existance check before let bindings are allowed to
                // overwrite each other, just like in rust.
                self.add_binding(&identifier, mutable, val.clone());
                Ok(val)
            },
            Statement::Empty => {
                // make fun of javascript
                unreachable!();
            },
        }
    }
    fn eval_expr(&mut self, expr_source: &ExpressionSource) -> Result<Rc<OrnVal>, RuntimeError> {
        let line = expr_source.line;
        let column = expr_source.column;
        let expr = (*expr_source).expr.clone();
        match expr {
            Expression::Fn { identifier, return_type, params, body } => {
                // if datatype is INFER, then try inferring it
                // then just return as is mostly :|
                return Ok(Rc::new(OrnVal::Fn {
                    identifier: identifier,
                    return_type: return_type,
                    params: params,
                    body: body,
                    env: self.frames.iter().map(|x| x.clone()).collect::<Vec<_>>(),
                    line: line,
                    column: column,
                }));
            },
            Expression::Binary { left, operator, right } => {
                let left = try!(self.eval_expr(left.borrow()));
                match operator {
                    BinaryOperator::Or => {
                        match left.borrow() {
                            &OrnVal::Bool(true) => {
                                return Ok(Rc::new(OrnVal::Bool(true)));
                            },
                            &OrnVal::Bool(false) => {
                                return self.eval_expr(right.borrow());
                            },
                            silly => {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::TypeError,
                                    line: line,
                                    column: column,
                                    msg: format!("Expected boolean value for logical or operation. Got {} :/", silly),
                                });
                            },
                        }
                    },
                    BinaryOperator::And => {
                        match left.borrow() {
                            &OrnVal::Bool(true) => {
                                return self.eval_expr(right.borrow());
                            },
                            &OrnVal::Bool(false) => {
                                return Ok(Rc::new(OrnVal::Bool(false)));
                            },
                            silly => {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::TypeError,
                                    line: line,
                                    column: column,
                                    msg: format!("Expected boolean value for logical and operation. Got {} :/", silly),
                                });
                            },
                        }
                    },
                    _ => {},
                }
                let right = try!(self.eval_expr(right.borrow()));
                match operator {
                    BinaryOperator::Equals => {
                        // this is complicated
                        // evaluate both left and right
                        // check types. if types are different, return false
                        // if types are literals, do simple equality check and return result
                        // else check if both are the same objects (do we even have those?)
                        match (left.borrow(), right.borrow()) {
                            (&OrnVal::Str(ref x), &OrnVal::Str(ref y)) => {
                                return Ok(Rc::new(OrnVal::Bool(x == y)));
                            },
                            (&OrnVal::Bool(ref x), &OrnVal::Bool(ref y)) => {
                                return Ok(Rc::new(OrnVal::Bool(x == y)));
                            },
                            (&OrnVal::UInt(ref x), &OrnVal::UInt(ref y)) => {
                                return Ok(Rc::new(OrnVal::Bool(x == y)));
                            },
                            (&OrnVal::Int(ref x), &OrnVal::Int(ref y)) => {
                                return Ok(Rc::new(OrnVal::Bool(x == y)));
                            },
                            (&OrnVal::Float(ref x), &OrnVal::Float(ref y)) => {
                                return Ok(Rc::new(OrnVal::Bool(x == y)));
                            },
                            (x @ &OrnVal::Fn { .. }, y @ &OrnVal::Fn { .. }) => {
                                return Ok(Rc::new(OrnVal::Bool(&*x as *const _ == &*y as *const _)));
                            },
                            (&_, &_) => {
                                return Ok(Rc::new(OrnVal::Bool(false)));
                            },
                        }
                    },
                    BinaryOperator::Add => {
                        match (left.borrow(), right.borrow()) {
                            (&OrnVal::Str(ref x), &OrnVal::Str(ref y)) => {
                                return Ok(Rc::new(OrnVal::Str({
                                    let mut c = x.clone();
                                    c.push_str(y);
                                    c
                                })));
                            },
                            (&OrnVal::UInt(ref x), &OrnVal::UInt(ref y)) => {
                                return Ok(Rc::new(OrnVal::UInt(x + y)));
                            },
                            (&OrnVal::UInt(ref x), &OrnVal::Float(ref y)) => {
                                return Ok(Rc::new(OrnVal::Float(*x as f64 + y)));
                            },
                            (&OrnVal::UInt(ref x), &OrnVal::Int(ref y)) => {
                                return Ok(Rc::new(OrnVal::Int(*x as i32 + y)));
                            },
                            (&OrnVal::Int(ref x), &OrnVal::Int(ref y)) => {
                                return Ok(Rc::new(OrnVal::Int(x + y)));
                            },
                            (&OrnVal::Int(ref x), &OrnVal::Float(ref y)) => {
                                return Ok(Rc::new(OrnVal::Float(*x as f64 + y)));
                            },
                            (&OrnVal::Int(ref x), &OrnVal::UInt(ref y)) => {
                                return Ok(Rc::new(OrnVal::Int(x + *y as i32)));
                            },
                            (&OrnVal::Float(ref x), &OrnVal::Float(ref y)) => {
                                return Ok(Rc::new(OrnVal::Float(x + y)));
                            },
                            (&OrnVal::Float(ref x), &OrnVal::UInt(ref y)) => {
                                return Ok(Rc::new(OrnVal::Float(x + *y as f64)));
                            },
                            (&OrnVal::Float(ref x), &OrnVal::Int(ref y)) => {
                                return Ok(Rc::new(OrnVal::Float(x + *y as f64)));
                            },
                            (ref x, ref y) => {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::TypeError,
                                    line: line,
                                    column: column,
                                    msg: format!("Cannot add {} and {}. I only add strings to strings and numbers to numbers. Perhaps try JavaScript instead? :)", x, y),
                                });
                            }
                        }
                    },
                    BinaryOperator::Subtract => {
                        return operate_on_numbers_magically!(left.borrow(), right.borrow(), Sub::sub, line, column);
                    },
                    BinaryOperator::Multiply => {
                        return operate_on_numbers_magically!(left.borrow(), right.borrow(), Mul::mul, line, column);
                    },
                    BinaryOperator::Divide => {
                        return operate_on_numbers_magically!(left.borrow(), right.borrow(), Div::div, line, column);
                    },
                    BinaryOperator::Modulo => {
                        return operate_on_numbers_magically!(left.borrow(), right.borrow(), Rem::rem, line, column);
                    },
                    BinaryOperator::GreaterThan => {
                        let r = compare_numbers_magically!(left.borrow(), right.borrow(), PartialOrd::partial_cmp, line, column).unwrap();
                        return Ok(Rc::new(OrnVal::Bool(r == Ordering::Greater)));
                    },
                    BinaryOperator::GreaterThanOrEqualTo => {
                        let r = compare_numbers_magically!(left.borrow(), right.borrow(), PartialOrd::partial_cmp, line, column).unwrap();
                        return Ok(Rc::new(OrnVal::Bool(r == Ordering::Greater || r == Ordering::Equal)));
                    },
                    BinaryOperator::LessThan => {
                        let r = compare_numbers_magically!(left.borrow(), right.borrow(), PartialOrd::partial_cmp, line, column).unwrap();
                        return Ok(Rc::new(OrnVal::Bool(r == Ordering::Less)));
                    },
                    BinaryOperator::LessThanOrEqualTo => {
                        let r = compare_numbers_magically!(left.borrow(), right.borrow(), PartialOrd::partial_cmp, line, column).unwrap();
                        return Ok(Rc::new(OrnVal::Bool(r == Ordering::Less || r == Ordering::Equal)));
                    },
                    _ => { unreachable!(); },
                }
            },
            Expression::Unary { operator, argument } => {
                let arg = try!(self.eval_expr(&argument));
                match operator {
                    UnaryOperator::Negate => {
                        // evaluate expression and type check to ensure it is boolean
                        // return negation
                        match arg.borrow() {
                            &OrnVal::Bool(ref x) => { return Ok(Rc::new(OrnVal::Bool(!x))); }
                            _ => {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::TypeError,
                                    line: line,
                                    column: column,
                                    msg: "Can only negate booleans.".to_string(),
                                });
                            },
                        }
                    },
                    UnaryOperator::Subtract => {
                        // evaluate expression and type check to ensure it is numerical
                        // return negative
                        return Ok(Rc::new(match arg.borrow() {
                            &OrnVal::UInt(ref x) => { OrnVal::Int(-(*x as i32)) },
                            &OrnVal::Int(ref x) => { OrnVal::Int(-x) },
                            &OrnVal::Float(ref x) => { OrnVal::Float(-x) },
                            ref shit => {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::TypeError,
                                    line: line,
                                    column: column,
                                    msg: format!("Can only find negative of numbers, not {}.", shit),
                                });
                            }
                        }));
                    },
                    UnaryOperator::Add => {
                        // evaluate expression and type check to ensure it is numerical
                        // return evaluated value
                        unimplemented!();
                    },
                }
            },
            Expression::If(cases) => {
                for (ref condition, ref consequence) in cases {
                    // evaluate condition and type check to ensure it is boolean
                    // if it is true, evaluate consequence in its own block and return
                    match try!(self.eval_expr(condition)).borrow() {
                        &OrnVal::Bool(true) => {
                            return self.eval_block(consequence);
                        },
                        &OrnVal::Bool(false) => { continue; },
                        _ => {
                            return Err(RuntimeError {
                                error_type: RuntimeErrorType::TypeError,
                                line: line,
                                column: column,
                                msg: "Expected boolean value for condition check. Got crap :|".to_string(),
                            });
                        }
                    }
                }
                return Ok(Rc::new(OrnVal::Bool(false)));
            },
            Expression::Assignment { ref left, ref right } => {
                // obtain pointer reference to left string
                // check if it is marked mutable
                // evaluate right expression
                // set value of left to right
                // return evaluated value
                let val = try!(self.eval_expr(right));
                for stack_ref in self.frames.iter().rev() {
                    let mut stack = stack_ref.borrow_mut();
                    match stack.scope.get_mut(left) {
                        Some(ref mut binding) => {
                            if binding.mutable {
                                binding.val = val.clone();
                                return Ok(val);
                            } else {
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::InitializationError,
                                    line: line,
                                    column: column,
                                    msg: format!("Won't change immutable variable {} kid.", left),
                                });
                            }
                        },
                        None => {
                            continue;
                        }
                    }
                }
                return Err(RuntimeError {
                    error_type: RuntimeErrorType::ReferenceError,
                    line: line,
                    column: column,
                    msg: format!("Variable {} is not defined kid.", left),
                });
            },
            Expression::Reference(ref id) => {
                // obtain pointer reference to id and return its value
                return self.get_value(id).ok_or(RuntimeError {
                    error_type: RuntimeErrorType::ReferenceError,
                    line: line,
                    column: column,
                    msg: format!("reference error bro. {} is not defined", id),
                });
            },
            Expression::Call { callee, args } => {
                // TODO: lol this is a terrible hack
                // FIXME when we get a real standard library
                match callee.as_ref().expr {
                    Expression::Reference(ref x) if x == "echo" => {
                        for arg in args.iter() {
                            println!("{}", try!(self.eval_expr(arg)));
                        }
                        return Ok(Rc::new(OrnVal::Bool(false)));
                    },
                    _ => {},
                };
                let f = try!(self.eval_expr(callee.borrow()));
                match f.borrow() {
                    &OrnVal::Fn { ref params, ref body, ref identifier, ref env, ref line, ref column, .. } => {
                        self.call_stack.push((*line, *column, identifier.to_string()));
                        assert_eq!(args.len(), params.len());
                        let mut call_frame = StackFrame::new();
                        for (arg, param) in args.iter().zip(params.iter()) {
                            call_frame.scope.insert(param.name.clone(), OrnBinding { mutable: false, val: try!(self.eval_expr(arg)) });
                        }
                        let mut stack = Stack::new();
                        for frame in env.iter() {
                            stack.frames.push(frame.clone());
                        }
                        stack.frames.push(Rc::new(RefCell::new(call_frame)));
                        let mut res = Rc::new(OrnVal::Bool(false));
                        for stmt in body.iter() {
                            res = try!(stack.eval_stmt(stmt));
                        }
                        self.call_stack.pop();
                        return Ok(res);
                    },
                    ref crap => {
                        return Err(RuntimeError {
                            error_type: RuntimeErrorType::TypeError,
                            line: line,
                            column: column,
                            msg: format!("Uhm, {} is not a function.", crap),
                        });
                    }
                }
            },
            Expression::StringLiteral(ref s) => {
                return Ok(Rc::new(OrnVal::Str(s.clone())));
            },
            Expression::NumberLiteral(ref n) => {
                // parse n as number and return value
                if n.contains('.') {
                    return Ok(Rc::new(OrnVal::Float(n.parse::<f64>().unwrap_or(0.0))));
                } else {
                    return Ok(Rc::new(OrnVal::UInt(n.parse::<u32>().unwrap_or(0))));
                }
            },
            Expression::BooleanLiteral(b) => {
                return Ok(Rc::new(OrnVal::Bool(b)));
            },
            Expression::Block(ref block) => {
                // evaluate each expression in a stack and return last expression's value somehow?
                return self.eval_block(block);
            },
        }
    }
    pub fn eval_block(&mut self, block: &Block) -> Result<Rc<OrnVal>, RuntimeError> {
        let new_frame = StackFrame::new();
        self.frames.push(Rc::new(RefCell::new(new_frame)));
        let mut ret = Ok(Rc::new(OrnVal::Bool(false)));
        for stmt in block.iter() {
            ret = self.eval_stmt(stmt);
        }
        self.frames.pop();
        return ret;
    }
}
