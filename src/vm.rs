use parser::{ Statement, Expression, ExpressionSource, Block, BinaryOperator, UnaryOperator, FunctionParameter, DataType, Parser };
use stdlib::get_amazing_orn_stdlib_as_stackframe;
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
    pub mutable: bool,
    /// Rc reference to the value pointed at by this binding
    pub val: Rc<OrnVal>,
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
    Array {
        data_type: DataType,
        values: RefCell<Vec<Rc<OrnVal>>>,
    },
    Mod(HashMap<String, Rc<OrnVal>>),
    BuiltIn {
        identifier: String,
        func: fn(&mut Stack, Vec<Rc<OrnVal>>) -> Result<Rc<OrnVal>, RuntimeError>,
    },
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
            &OrnVal::Array { ref values, .. } => {
                write!(f, "[{}]", values.borrow().iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "))
            },
            &OrnVal::Mod(ref module) => {
                write!(f, "<inbuilt module>")
            },
            &OrnVal::BuiltIn { ref identifier, .. } => {
                write!(f, "<builtin function {}>", identifier)
            },
        }
    }
}

/// A stackframe represents a scope object basically. This might get more
/// things in future, but presently we only put bindings of a scope in it.
pub struct StackFrame {
    /// The hashmap storing bindings by their names
    pub scope: HashMap<String, OrnBinding>,
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
    /// Stored in a refcell because the call_stack is globally shared across
    /// all function calls.
    pub call_stack: Rc<RefCell<Vec<(u32, u32, String)>>>,
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
            (x @ &OrnVal::Array { .. }, y @ &OrnVal::Array { .. }) => { &*x as *const _ == &*y as *const _ },
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
        Stack {
            frames: vec![Rc::new(RefCell::new(get_amazing_orn_stdlib_as_stackframe()))],
            call_stack: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn new_child(call_stack: Rc<RefCell<Vec<(u32, u32, String)>>>) -> Stack {
        Stack { frames: vec![Rc::new(RefCell::new(StackFrame::new()))], call_stack: call_stack }
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
                            (&OrnVal::Array { data_type: ref x_type, values: ref x_values }, &OrnVal::Array { data_type: ref y_type, values: ref y_values }) => {
                                if x_type != y_type {
                                    return Err(RuntimeError {
                                        error_type: RuntimeErrorType::TypeError,
                                        line: line,
                                        column: column,
                                        msg: format!("Concatenating arrays requires both to contain the same type of elements! You had types {} and {} which won't work :P", x_type, y_type),
                                    });
                                }
                                let mut new_vec = x_values.borrow().clone();
                                new_vec.extend(y_values.borrow().clone());
                                return Ok(Rc::new(OrnVal::Array {
                                    data_type: x_type.clone(),
                                    values: RefCell::new(new_vec),
                                }));
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

            Expression::Member { ref parent, ref member } => {
                let parent = try!(self.eval_expr(parent));
                match parent.borrow() {
                    &OrnVal::Mod(ref module) => {
                        match module.get(member) {
                            Some(mem) => { Ok(mem.clone()) },
                            None => {
                                Err(RuntimeError {
                                    error_type: RuntimeErrorType::ReferenceError,
                                    line: line,
                                    column: column,
                                    msg: format!("There is no property {} on this thing!", member),
                                })
                            }
                        }
                    },
                    parent => {
                        Err(RuntimeError {
                            error_type: RuntimeErrorType::ReferenceError,
                            line: line,
                            column: column,
                            msg: format!("Only modules have properties as of now. {} doesn't :)", parent),
                        })
                    },
                }
            },

            Expression::Call { callee, args } => {
                let (func, args) = try!(self.desugar_call_expr(&callee, args));
                match func.borrow() {
                    &OrnVal::Fn { .. } => { /* fine */ },
                    &OrnVal::BuiltIn { .. } => { /* fine too */ },
                    ref crap => {
                        // heathens
                        return Err(RuntimeError {
                            error_type: RuntimeErrorType::TypeError,
                            line: line,
                            column: column,
                            msg: format!("{} is not a function. y u no get it >:(", crap),
                        });
                    },
                }
                self.call_user_func(func, args)
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

            Expression::Array(ref exprs) => {
                let mut values = vec![];
                for ref expr in exprs.iter() {
                    values.push(try!(self.eval_expr(expr)));
                }
                return Ok(Rc::new(OrnVal::Array {
                    data_type: DataType::INFER,
                    values: RefCell::new(values),
                }));
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

    /// Given the parts of a call expression, this function desugars them if the callee is a member
    /// expression which needs to desugar
    ///
    /// i.e., it converts foo.bar(...) to <Type(foo)>.bar(foo, ...). It leaves the other things
    /// alone and the return type is a tuple containing an ornval which is guaranteed to be either
    /// of the variant Fn or BuiltIn, and a vector of ornvals to pass to the function.
    pub fn desugar_call_expr(&mut self, callee: &ExpressionSource, args: Vec<ExpressionSource>)
        -> Result<(Rc<OrnVal>, Vec<Rc<OrnVal>>), RuntimeError>
    {
        let line = callee.line;
        let column = callee.column;

        // helper to evaluate arguments since we need to optionally mutate them later on when we
        // push the "context" caller at the start
        macro_rules! eval_args {
            ($self_:ident, $args:expr) => {
                {
                    // this cannot use map because then the try! macro will return from the map
                    // callback and we'd end up with an array of Results instead of a proper array
                    // of arguments.
                    let mut evaled_args = Vec::new();
                    for arg in args.iter() {
                        evaled_args.push(try!(self.eval_expr(arg)));
                    }
                    evaled_args
                }
            }
        }

        // the fun begins!
        match (*callee).expr.clone() {
            // if this is a member expression
            Expression::Member { parent, member } => {
                // try evaluating the parent first
                let paren = try!(self.eval_expr(parent.borrow()));

                // if the parent is an orn module...
                if let &OrnVal::Mod(ref module) = paren.borrow() {
                    // we call the method as a static function as is and no need to desugar
                    // anything at all
                    let func = match module.get(&member) {
                        Some(mem) => { mem.clone() },
                        None => {
                            return Err(RuntimeError {
                                error_type: RuntimeErrorType::ReferenceError,
                                line: line,
                                column: column,
                                msg: format!("No method {} found :|", member),
                            });
                        },
                    };
                    Ok((func, eval_args!(self, args)))
                } else {
                    // otherwise, we first find what global "module" corresponds to the value on
                    // which this method was called.
                    let module_name = match paren.borrow() {
                        &OrnVal::Bool(_) => { "Bool" },
                        &OrnVal::Str(_) => { "Str" },
                        &OrnVal::Array { .. } => { "Array" },
                        &OrnVal::UInt(_) => { "UInt" },
                        &OrnVal::Int(_) => { "Int" },
                        &OrnVal::Float(_) => { "Float" },
                        &OrnVal::Fn { .. } | &OrnVal::BuiltIn { .. } => { "Fn" },
                        &OrnVal::Mod(_) => { unreachable!(); },
                    };

                    // we retrieve that module from the global scope
                    let ref module_ornval = self
                                    .frames
                                    .get(0)
                                    .expect("Getting global environment for extraction of prototype")
                                    .as_ref()
                                    .borrow()
                                    .scope
                                    .get(module_name)
                                    .expect("Getting prototype from global environment")
                                    .borrow()
                                    .val.clone();

                    // ensure that it is a module not something else which got meddled with
                    let module = match module_ornval.as_ref() {
                        &OrnVal::Mod(ref module) => { module },
                        _ => { unreachable!(); },
                    };

                    // and retrieve the function from that module which was called
                    let func = match module.get(&member) {
                        Some(mem) => { mem.clone() },
                        None => {
                            return Err(RuntimeError {
                                error_type: RuntimeErrorType::ReferenceError,
                                line: line,
                                column: column,
                                msg: format!("No method {} found :|", member),
                            });
                        },
                    };

                    // if the method is valid, we now evaluate the arguments
                    let mut evaled_args = eval_args!(self, args);

                    // and push the "context" object to the front of the arguments array
                    evaled_args.insert(0, paren.clone());

                    // and return our desugared result!
                    Ok((func, evaled_args))
                }
            },

            // the following expressions can never return callable functions, hence we error out
            // early on these
            Expression::BooleanLiteral(_) | Expression::StringLiteral(_) | Expression::NumberLiteral(_) | Expression::Unary { .. } | Expression::Array(_) => {
                Err(RuntimeError {
                    error_type: RuntimeErrorType::TypeError,
                    line: line,
                    column: column,
                    msg: format!("Random crap is not a valid function. FFS people, stop being retards."),
                })
            },

            // for all other expressions, we don't need desugaring but they might still be valid
            // functions
            expr => {
                Ok((try!(self.eval_expr(&callee)), eval_args!(self, args)))
            },
        }
    }

    /// Calls a function with the given arguments. Both builtins and userland functions are
    /// acceptable. Anything else will return a RuntimeError::TypeError
    pub fn call_user_func(&mut self, val: Rc<OrnVal>, args: Vec<Rc<OrnVal>>) -> Result<Rc<OrnVal>, RuntimeError> {
        match val.borrow() {
            &OrnVal::Fn { ref params, ref body, ref identifier, ref env, ref line, ref column, .. } => {
                // push function name and location to call stack
                self.call_stack.borrow_mut().push((*line, *column, identifier.to_string()));

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
                for (arg, param) in args.into_iter().zip(params.iter()) {
                    call_frame.scope.insert(param.name.clone(), OrnBinding { mutable: false, val: arg });
                }

                // create a new child stack for execution
                let mut stack = Stack::new_child(self.call_stack.clone());

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
                self.call_stack.borrow_mut().pop();
                Ok(res)
            },
            &OrnVal::BuiltIn { ref identifier, ref func } => {
                self.call_stack.borrow_mut().push((0, 0, identifier.to_string()));
                let res = try!(func(self, args));
                self.call_stack.borrow_mut().pop();
                Ok(res)
            },
            val => {
                Err(RuntimeError {
                    error_type: RuntimeErrorType::TypeError,
                    line: 0,
                    column: 0,
                    msg: format!("{} is not a function", val),
                })
            },
        }
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
                            err_buf.push_str(&format!("{}:{} {}: {}\n", o.line, o.column, o.error_type, o.msg));

                            // and stack trace which took us so far
                            for &(line, column, ref func) in self.call_stack.as_ref().borrow().iter() {
                                err_buf.push_str(&format!("{}:{} at function {}\n", line, column, func));
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
