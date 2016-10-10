use parser::{ Statement, Expression, ExpressionSource, Block, BinaryOperator, UnaryOperator, FunctionParameter, DataType, Parser };
use std::rc::Rc;
use std::cell::Ref;
use std::cell::RefCell;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt;
use std::cmp::Ordering;
use std::ops::{ Sub, Mul, Div, Rem };


/// A binding is held by a scope object in a hashmap.
///
/// Each binding is uniquely held and owned by one scope.
///
/// Note that bindings are what dictate whether something is mutable or not.
/// Values are always mutable, but bindings are "gates" to their mutation
/// and access.
pub struct OrnBinding {
    /// Indicates whether the binding is mutable or not
    mutable: bool,
    /// Rc reference to the value pointed at by this binding
    val: Rc<OrnVal>,
}

/// OrnVal is the generic container for all kinds of types of values that
/// are possible to exist in userland. References to these are stored in
/// bindings, and the VM API functions return those references. But we
/// generally never pass raw OrnVals around.
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

/// A stackframe represents a scope object basically. This might get more
/// things in future, but presently we only put bindings of a scope in it.
pub struct StackFrame {
    /// The hashmap storing bindings by their names
    scope: HashMap<String, OrnBinding>,
}

/// A stack is a stack of frames. Everytime a scope is entered, a stackframe
/// is created and pushed onto the stack. The stack doesn't take pure ownership
/// of the frames though, so a stack could be duplicated on the heap and stored
/// as a "live" environment (which is what closures do).
/// When any block exits scope, its frame reference is removed from the stack.
pub struct Stack {
    pub frames: Vec<Rc<RefCell<StackFrame>>>,
    /// The call_stack vector stores a stack of function names we are presently
    /// executing under.
    /// When a function exits scope, its name is removed from the call stack.
    pub call_stack: Vec<(u32, u32, String)>,
}

/// We use enums instead of strings here because I think enums take lesser space
/// and just fit generically well. I might be wrong here, but this works fine.
/// Also provides a bit of type-safety I guess.
pub enum RuntimeErrorType {
    /// Indicates use of an un-initialized binding
    ReferenceError,
    /// Indicates mismatch of types
    TypeError,
    /// Indicates a problem occurred while initializing a binding
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

/// Representation of a runtime error.
///
/// Note that we halt execution as soon as an error occurs and the
/// only "trace" we kept is the call_stack which is kept in the current
/// stack.
pub struct RuntimeError {
    pub error_type: RuntimeErrorType,
    pub msg: String,
    pub line: u32,
    pub column: u32,
}

/// generic macro to apply a mathematical operation on two ornval references
#[macro_export]
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

/// generic macro for mathematical comparison of ornvalues
#[macro_export]
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

/// generic macro for checking value or reference equality
#[macro_export]
macro_rules! check_value_equality {
    ($self_:ident, $left:expr, $right:expr) => {
        match ($left, $right) {
            (&OrnVal::Str(ref x), &OrnVal::Str(ref y)) => { x == y },
            (&OrnVal::Bool(ref x), &OrnVal::Bool(ref y)) => { x == y },
            (&OrnVal::UInt(ref x), &OrnVal::UInt(ref y)) => { x == y },
            (&OrnVal::Int(ref x), &OrnVal::Int(ref y)) => { x == y },
            (&OrnVal::Float(ref x), &OrnVal::Float(ref y)) => { x == y },
            (x @ &OrnVal::Fn { .. }, y @ &OrnVal::Fn { .. }) => { &*x as *const _ == &*y as *const _ },
            (&_, &_) => { false },
        }
    }
}

impl StackFrame {
    /// Creates a new StackFrame
    pub fn new() -> StackFrame {
        StackFrame { scope: HashMap::new() }
    }
}

impl Stack {
    /// Creates a new empty Stack
    ///
    /// To evaluate things in the context of this stack, use Stack.eval_expr or Stack.eval_stmt
    pub fn new() -> Stack {
        Stack { frames: vec![Rc::new(RefCell::new(StackFrame::new()))], call_stack: Vec::new() }
    }

    /// Adds a binding to the top most frame in the current stack
    pub fn add_binding(&mut self, id: &str, mutable: bool, val: Rc<OrnVal>) {
        self
            .frames
            .last()
            .expect("getting last frame while adding binding")
            .borrow_mut()
            .scope
            .insert(id.to_string(), OrnBinding { mutable: mutable, val: val });
    }

    /// Traverses entire scope chain to get the value of a binding by name
    pub fn get_value(&self, id: &str) -> Option<Rc<OrnVal>> {
        for frame_ref in self.frames.iter().rev() {
            let frame: Ref<StackFrame> = frame_ref.as_ref().borrow();
            match frame.scope.get(id) {
                Some(ref binding) => { return Some(binding.val.clone()); },
                None => { continue; },
            }
        }
        None
    }

    /// Given a reference to a statement object, this function clones it and evaluates it
    /// under the current execution context
    pub fn eval_stmt(&mut self, stmt: &Statement) -> Result<Rc<OrnVal>, RuntimeError> {
        match (*stmt).clone() {
            Statement::ExpressionStatement(expr_source) => {
                let line = expr_source.line;
                let column = expr_source.column;
                match expr_source.expr {
                    // function expressions in statements are treated as special since they
                    // are a binding too (an immutable one)
                    Expression::Fn { identifier, params, return_type, body } => {
                        // get current scope frame
                        let mut frame = self
                                            .frames
                                            .last()
                                            .expect("getting last frame while parsing fn expression statement")
                                            .as_ref()
                                            .borrow_mut();
                        // check if a binding with the same name already exists
                        match frame.scope.get(&identifier) {
                            Some(_) => { // bail if so
                                return Err(RuntimeError {
                                    error_type: RuntimeErrorType::InitializationError,
                                    line: line,
                                    column: column,
                                    msg: format!("There is already a binding by the name \"{}\" in scope. Pick another name?", identifier),
                                });
                            },
                            None => { // else create new binding!
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
                                // return a reference to the created ornval
                                return Ok(val);
                            },
                        }
                    },
                    _ => { // just return the result of evaluating the expression as is
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
                unimplemented!();
            },
        }
    }

    /// Given a reference to an expression, this function clones and evaluates the expression
    /// in the current execution context
    fn eval_expr(&mut self, expr_source: &ExpressionSource) -> Result<Rc<OrnVal>, RuntimeError> {
        let line = expr_source.line;
        let column = expr_source.column;
        let expr = (*expr_source).expr.clone();
        match expr {
            // a function expression is just copied to an ornval with the environment
            // and returned as is. not much sideeffects going on here
            Expression::Fn { identifier, return_type, params, body } => {
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

            // binary expression evaluation!
            Expression::Binary { left, operator, right } => {
                // first evaluate the left side which is important
                let left = try!(self.eval_expr(left.borrow()));

                // check if the operator is a logical type
                // in which case we short-circuit the evaluation of the right hand
                // side so that it is evaluated only if required
                match operator {
                    // in case of or
                    BinaryOperator::Or => {
                        match left.borrow() {
                            // we stop evaluation if left side is true
                            &OrnVal::Bool(true) => {
                                return Ok(Rc::new(OrnVal::Bool(true)));
                            },
                            // but continue evaluation if right side isn't
                            &OrnVal::Bool(false) => {
                                // TODO: type check for boolean
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
                    // in case of and
                    BinaryOperator::And => {
                        match left.borrow() {
                            // we continue evaluation only if the left side is true
                            &OrnVal::Bool(true) => {
                                // TODO: type check as boolean?
                                return self.eval_expr(right.borrow());
                            },
                            // and return false early otherwise
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
                    // continue further execution for other operators
                    _ => {},
                }
                // for all other operators, we absolutely need both left and right, so evalute
                // right hand side expression too now
                let right = try!(self.eval_expr(right.borrow()));
                match operator {
                    BinaryOperator::Equals => {
                        return Ok(Rc::new(OrnVal::Bool(check_value_equality!(self, left.borrow(), right.borrow()))));
                    },
                    BinaryOperator::Unequals => {
                        return Ok(Rc::new(OrnVal::Bool(!check_value_equality!(self, left.borrow(), right.borrow()))));
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
                    BinaryOperator::Or | BinaryOperator::And => {
                        // since we just operated for these two logical operators above, they will
                        // not be matched again
                        unreachable!();
                    },
                }
            },

            // simple unary expressions!
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
                        // TODO: reconsider if this is really needed?
                        unimplemented!();
                    },
                }
            },

            // conditionals! yay!
            Expression::If(cases) => {
                // for each condition and consequence pair in cases...
                for (ref condition, ref consequence) in cases {
                    // evaluate condition and type check to ensure it is boolean
                    // if it is true, evaluate consequence in its own block and return
                    match try!(self.eval_expr(condition)).borrow() {
                        &OrnVal::Bool(true) => {
                            return self.eval_block(consequence);
                        },
                        // otherwise check next condition
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
                // until everything fails, at which point we return false
                return Ok(Rc::new(OrnVal::Bool(false)));
            },

            Expression::Assignment { ref left, ref right } => {
                // TODO: value should be evaluted after checking binding presence
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

                // evaluate callee to obtain reference to function
                let f = try!(self.eval_expr(callee.borrow()));
                match f.borrow() {
                    // if it is indeed a function...
                    &OrnVal::Fn { ref params, ref body, ref identifier, ref env, ref line, ref column, .. } => {
                        // push function name and location to call stack
                        self.call_stack.push((*line, *column, identifier.to_string()));

                        // assert adequate number of arguments are passed
                        assert_eq!(args.len(), params.len());

                        // TODO: type check parameter types to match arguments passed!

                        // create a new stack frame for storing arguments and a reference to the
                        // function itself
                        let mut call_frame = StackFrame::new();
                        // TODO: also add function itself to this frame to allow recursion in
                        // function expressions

                        // push each argument passed by its name from the corresponding parameter
                        // to the above frame
                        for (arg, param) in args.iter().zip(params.iter()) {
                            call_frame.scope.insert(param.name.clone(), OrnBinding { mutable: false, val: try!(self.eval_expr(arg)) });
                        }

                        // create a new stack for execution
                        let mut stack = Stack::new();

                        // restore environment of function to where it was declared
                        for frame in env.iter() {
                            stack.frames.push(frame.clone());
                        }

                        // add our argument frame to the above stack
                        stack.frames.push(Rc::new(RefCell::new(call_frame)));

                        // start execution and record result of each statement (to return last one
                        // in the end)
                        let mut res = Rc::new(OrnVal::Bool(false));
                        for stmt in body.iter() {
                            res = try!(stack.eval_stmt(stmt));
                        }

                        // remove the added entry to call stack before exiting
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
                return self.eval_block(block);
            },
        }
    }

    /// Given a reference to a block, this function clones it and evaluates it
    pub fn eval_block(&mut self, block: &Block) -> Result<Rc<OrnVal>, RuntimeError> {
        // create a new stack frame
        let new_frame = StackFrame::new();

        // push the frame to current execution context
        self.frames.push(Rc::new(RefCell::new(new_frame)));

        // variable to record value of each statement execution so we can return the result of the
        // last successfully executed statement as return value of the block
        let mut ret = Ok(Rc::new(OrnVal::Bool(false)));
        for stmt in block.iter() {
            ret = self.eval_stmt(stmt);
        }

        // remove frame from the execution context
        self.frames.pop();
        return ret;
    }

    pub fn eval(&mut self, code: &String) -> Result<Rc<OrnVal>, String> {
        // create parse stream
        let p = Parser::new(&code);

        let mut res = Rc::new(OrnVal::Bool(false));
        // start parsing!
        for stmt in p {
            match stmt {
                Ok(stmt) => {
                    // evaluate as they come!
                    match self.eval_stmt(&stmt) {
                        Ok(val) => {
                            res = val;
                        },
                        Err(o) => {
                            // bad user :(
                            let mut err_buf = String::new();
                            // the error which occured
                            err_buf.push_str(&format!("{}:{} {}: {}", o.line, o.column, o.error_type, o.msg));

                            // and stack trace which took us so far
                            for &(line, column, ref func) in &self.call_stack {
                                err_buf.push_str(&format!("{}:{} at function {}", line, column, func));
                            }

                            return Err(err_buf);
                        },
                    }
                },
                Err(o) => {
                    // why people no write code properly :(
                    return Err(format!("{}:{} SyntaxError: {}", o.line, o.column, o.msg));
                },
            }
        }

        return Ok(res);
    }
}
