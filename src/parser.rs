use std::iter::Peekable;
use std::fmt;

use lexer::{ Token, Lexeme, Keyword, Lexer };

// The following structures technically represent sort of an AST of the source code but they
// actually represent more of an IR for the code that gets interpreted later on in the pipeline.
// Preserving source structure is not the aim here, but correctly mapping to interpretable
// instructions while preserving behavior is.

#[derive(Clone)]
pub enum Statement {
    Let { mutable: bool, identifier: String, data_type: DataType, initializer: ExpressionSource },
    ExpressionStatement(ExpressionSource),
    Empty,
    // TODO: add rule statement
}

#[derive(Clone)]
pub enum Expression {
    Fn { identifier: String, params: Vec<FunctionParameter>, return_type: DataType, body: Block },
    Binary { left: Box<ExpressionSource>, operator: BinaryOperator, right: Box<ExpressionSource> },
    Unary { operator: UnaryOperator, argument: Box<ExpressionSource> },
    If(Vec<(ExpressionSource, Block)>),
    Assignment { left: String, right: Box<ExpressionSource> },
    Reference(String),
    Call { callee: Box<ExpressionSource>, args: Vec<ExpressionSource> },
    StringLiteral(String),
    NumberLiteral(String),
    BooleanLiteral(bool),
    Block(Block),
}

#[derive(Clone)]
pub struct ExpressionSource {
    pub line: u32,
    pub column: u32,
    pub expr: Expression,
}

pub type Block = Vec<Statement>;

#[derive(Clone)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Equals,
    Unequals,
    LessThan,
    GreaterThan,
    LessThanOrEqualTo,
    GreaterThanOrEqualTo,
    Or,
    And,
}

#[derive(Clone)]
pub enum UnaryOperator {
    Add,
    Subtract,
    Negate,
}

#[derive(Clone)]
pub struct FunctionParameter {
    pub name: String,
    pub data_type: DataType,
}

impl fmt::Display for FunctionParameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.data_type)
    }
}

#[derive(Clone)]
pub enum DataType {
    UInt,
    Int,
    Str,
    Float,
//    Fn { return_type: Box<DataType>, params: Vec<DataType> },
    Bool,
    INFER,
}

impl fmt::Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &DataType::UInt => { write!(f, "uint") },
            &DataType::Int => { write!(f, "int") },
            &DataType::Str => { write!(f, "str") },
            &DataType::Float => { write!(f, "float") },
            &DataType::Bool => { write!(f, "bool") },
            &DataType::INFER => { write!(f, "infer") },
        }
    }
}

pub struct SyntaxError {
    pub line: u32,
    pub column: u32,
    pub msg: String,
}

fn keyword_to_data_type(k: &Keyword) -> Result<DataType, ()> {
    match k {
        &Keyword::UInt => {
            Ok(DataType::UInt)
        },
        &Keyword::Int => {
            Ok(DataType::Int)
        },
        &Keyword::Float => {
            Ok(DataType::Float)
        },
        &Keyword::Bool => {
            Ok(DataType::Bool)
        },
        &Keyword::Str => {
            Ok(DataType::Str)
        },
        _ => {
            Err(())
        }
    }
}

macro_rules! punctuator_to_unary_operator {
    ($self_:ident, $p:expr, $line:expr, $column:expr) => {
        match $p {
            &Token::Punctuator('+') => {
                UnaryOperator::Add
            },
            &Token::Punctuator('-') => {
                UnaryOperator::Subtract
            },
            &Token::Punctuator('!') => {
                UnaryOperator::Negate
            },
            ref tok => {
                return Err(SyntaxError {
                    line: $line,
                    column: $column,
                    msg: format!("Unexpected token {}. Expected data type!", tok),
                });
            }
        }
    }
}

pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
}

fn extract_token(lexeme: Lexeme) -> Token {
    lexeme.token
}

fn extract_token_ref<'a>(lexeme: &'a Lexeme) -> &'a Token {
    &lexeme.token
}

macro_rules! expect_and_consume_token {
    ($self_:ident, $token_pattern:pat, $failure_msg:expr) => {
        let lexeme = match $self_.lexer.next() {
            Some(l) => { l },
            None => {
                return Err(SyntaxError {
                    line: 0,
                    column: 0,
                    msg: format!("Unexpected EOF. Expected {}. {}", stringify!($token_pattern), $failure_msg),
                });
            },
        };
        match lexeme.token {
            $token_pattern => { /* yay this is valid! */ },
            tok => {
                return Err(SyntaxError {
                    line: lexeme.line,
                    column: lexeme.column,
                    msg: format!("Unexpected token {}. Expected {}. {}", tok, stringify!($token_pattern), $failure_msg),
                });
            },
        }
    };
}

macro_rules! expect_identifier {
    ($self_:ident, $failure_msg:expr) => {
        {
            let (line, column) = current_location!($self_);
            let lexeme = match $self_.lexer.next() {
                Some(l) => { l },
                None => {
                    return Err(SyntaxError {
                        line: line,
                        column: column,
                        msg: format!("Unexpected EOF. Expected identifier. {}", $failure_msg),
                    });
                },
            };
            match lexeme.token {
                Token::Unknown(id) => { id },
                tok => {
                    return Err(SyntaxError {
                        line: lexeme.line,
                        column: lexeme.column,
                        msg: format!("Unexpected token {}. Expected identifier. {}", tok, $failure_msg),
                    });
                },
            }
        }
    }
}

macro_rules! expect_datatype {
    ($self_:ident, $failure_msg:expr) => {
        {
            let lexeme = match $self_.lexer.next() {
                Some(l) => { l },
                None => {
                    return Err(SyntaxError {
                        line: 0,
                        column: 0,
                        msg: format!("Unexpected EOF. Expected data type. {}", $failure_msg),
                    });
                },
            };
            match lexeme.token {
                Token::Keyword(ref k) => {
                    match keyword_to_data_type(k) {
                        Ok(dt) => { dt },
                        Err(_) => {
                            return Err(SyntaxError {
                                line: lexeme.line,
                                column: lexeme.column,
                                msg: format!("Unexpected keyword {}. Expected data type. {}", k, $failure_msg),
                            });
                        },
                    }
                },
                tok => {
                    return Err(SyntaxError {
                        line: lexeme.line,
                        column: lexeme.column,
                        msg: format!("Unexpected token {}. Expected data type. {}", tok, $failure_msg),
                    });
                },
            }
        }
    }
}

macro_rules! check_and_consume_token {
    ($self_:ident, $token_pattern:pat) => {
        if let Some(&$token_pattern) = $self_.lexer.peek().map(extract_token_ref) {
            $self_.lexer.next();
            true
        } else {
            false
        }
    }
}

macro_rules! check_and_consume_punctuated_datatype {
    ($self_:ident) => {
        if let Some(&Token::Punctuator(':')) = $self_.lexer.peek().map(extract_token_ref) {
            $self_.lexer.next(); // consume punctuator
            expect_datatype!($self_, "If you don't wish to specify a type, please leave out the previous colon!")
        } else {
            DataType::INFER
        }
    }
}

macro_rules! expect_token_and_retrieve_location {
    ($self_:ident, $token_pattern:pat, $failure_msg:expr) => {
        match $self_.lexer.next() {
            Some(lex) => {
                if let $token_pattern = lex.token {
                    (lex.line, lex.column)
                } else {
                    return Err(SyntaxError {
                        line: lex.line,
                        column: lex.column,
                        msg: format!("Unexpected {}. Expected {}. {}", lex.token, stringify!($token_pattern), $failure_msg),
                    });
                }
            },
            None => {
                return Err(SyntaxError {
                    line: 0,
                    column: 0,
                    msg: format!("Unexpected EOF. Expected {}. {}", stringify!($token_pattern), $failure_msg),
                });
            },
        }
    }
}

macro_rules! current_location {
    ($self_:ident) => {
        match $self_.lexer.peek() {
            Some(ref x) => {
                (x.line, x.column)
            },
            None => {
                (0, 0)
            }
        }
    }
}
 
impl<'a> Parser<'a> {
    pub fn new(src: &'a String) -> Parser<'a> {
        Parser { lexer: Lexer::new(src).peekable() }
    }
    
    fn match_let_stmt(&mut self) -> Result<Statement, SyntaxError> {
        expect_token_and_retrieve_location!(self, Token::Keyword(Keyword::Let), "I was told to expect a let binding :|");

        // check if next is mut
        let mutable = check_and_consume_token!(self, Token::Keyword(Keyword::Mut));
        
        // now we only expect an id
        let id = expect_identifier!(self, "What should the variable's name be? :)");

        // maybe next follows a type
        let data_type = check_and_consume_punctuated_datatype!(self);

        // must have '=' now
        expect_and_consume_token!(self, Token::Punctuator('='), "Let declarations must have an initial assignment value!");

        Ok(Statement::Let {
            mutable: mutable,
            identifier: id,
            data_type: data_type,
            initializer: try!(self.match_expression()),
        })
    }

    fn match_fn_expr(&mut self) -> Result<ExpressionSource, SyntaxError> {
        let (line, column) = expect_token_and_retrieve_location!(self, Token::Keyword(Keyword::Fn), "I was told to expect a function :|");

        let id = expect_identifier!(self, "What should the function's name be? :)");
    
        expect_and_consume_token!(self, Token::Punctuator('('), "Function declaration must have an explicit parameter list, even if empty!");
        
        let mut params = vec![];
        loop {
            if let Some(&Token::Punctuator(')')) = self.lexer.peek().map(extract_token_ref) {
                self.lexer.next();
                break;
            }
            if let Some(&Token::Punctuator(',')) = self.lexer.peek().map(extract_token_ref) {
                self.lexer.next();
                continue;
            }
        
            // match parameter name
            let id = expect_identifier!(self, "What should the parameter's name be? :)");
            
            // check if next token is colon indicating a type follows
            let dt = check_and_consume_punctuated_datatype!(self);
            
            params.push(FunctionParameter {
                name: id,
                data_type: dt,
            });
        }

        // check if return type ahead
        let ret_type = if let Some(&Token::Punctuator('-')) = self.lexer.peek().map(extract_token_ref) {
            self.lexer.next(); // consume punctuator
            expect_and_consume_token!(self, Token::Punctuator('>'), "Please complete the arrow!");
            expect_datatype!(self, "If you don't wish to specify a type, please leave out the previous colon!")
        } else {
            DataType::INFER
        };
        
        Ok(ExpressionSource {
            line: line,
            column: column,
            expr: Expression::Fn {
                identifier: id,
                params: params,
                return_type: ret_type,
                // TODO: somehow tell advancer that we are in a function
                // and we should not accept rule statements?
                body: try!(self.match_block_stmt("Functions must have a body to execute! They are blocks of code which start with { and end in } :)")),
            },
        })
    }

    fn match_if_expr(&mut self) -> Result<ExpressionSource, SyntaxError> {
        let (line, column) = expect_token_and_retrieve_location!(self, Token::Keyword(Keyword::If), "I was told to expect an if chain :|");

        let mut cases: Vec<(ExpressionSource, Block)> = vec![];

        cases.push((try!(self.match_expression()), try!(self.match_block_stmt("If statements need a block!"))));
        
        loop {
            if check_and_consume_token!(self, Token::Keyword(Keyword::Else)) {
                // else of else if ahead
                if check_and_consume_token!(self, Token::Keyword(Keyword::If)) {
                    // else if confirmed
                    cases.push((try!(self.match_expression()), try!(self.match_block_stmt("Else if branches need a block!"))));
                    // there could be more branches, so continue
                    continue;
                } else {
                    // else confirmed
                    // once we get to an else, the if branch is terminated
                    // no elses or elifs could follow
                    let fake_true = ExpressionSource {
                        line: 0,
                        column: 0,
                        expr: Expression::BooleanLiteral(true),
                    };
                    cases.push((fake_true, try!(self.match_block_stmt("Else branches need a block!"))));
                    return Ok(ExpressionSource {
                        line: line,
                        column: column,
                        expr: Expression::If(cases),
                    });
                }
            }
            return Ok(ExpressionSource {
                line: line,
                column: column,
                expr: Expression::If(cases),
            });
        }
    }

    fn match_block_stmt(&mut self, failure_msg: &'static str) -> Result<Block, SyntaxError> {
        expect_and_consume_token!(self, Token::Punctuator('{'), failure_msg);
        self.continue_block_stmt()
    }

    fn continue_block_stmt(&mut self) -> Result<Block, SyntaxError> {
        // called after consuming the initial brace
        let mut block: Block = vec![];

        loop {
            // if closing
            if let Some(&Token::Punctuator('}')) = self.lexer.peek().map(extract_token_ref) {
                // consume closing brace
                self.lexer.next();
                // and exit
                return Ok(block);
            }

            // else consume statement
            let stmt = match try!(self.advance_from_idle_state()) {
                Some(stmt) => { stmt },
                None => { return Ok(block); },
            };
            block.push(stmt);
        }
    }

    fn continue_rule(&mut self) -> Result<Statement, SyntaxError> {
        unimplemented!();
    }

    fn match_expression(&mut self) -> Result<ExpressionSource, SyntaxError> {
        // this is really really hard, but lets see
        // we need an operable terminal to start with. lets call it expr
        // an operable expr is like a "complete" token on which you can make
        // compound expressions like call expressions, binary expressions etc.
        let (line, column) = current_location!(self);
        let mut expr = match self.lexer.peek().map(extract_token_ref) {
            Some(&Token::Punctuator(ch)) if ch == '+' || ch == '-' || ch == '!' => {
                self.lexer.next(); // consume operator
                // start unary expression
                ExpressionSource {
                    line: line,
                    column: column,
                    expr: Expression::Unary {
                        operator: punctuator_to_unary_operator!(self, &Token::Punctuator(ch), line, column),
                        argument: Box::new(try!(self.match_expression())),
                    },
                }
            },
            Some(&Token::Punctuator('(')) => {
                self.lexer.next();
                // parenthesixed expression
                // for this, we just reset the matching procedure (by recursing) and at
                // the end, we match a closing parenthesis
                let expr = try!(self.match_expression());
                expect_and_consume_token!(self, Token::Punctuator(')'), "Parenthesised expressions must end with a closing parenthesis!");
                expr
            },
            Some(&Token::Punctuator('{')) => {
                self.lexer.next();
                // block expression
                // similar to parenthesis expression, we reset by recursing and match a closing
                // brace at the end. except in this case, the continue_block_stmt procedure does
                // that for us and we don't :)
                ExpressionSource {
                    line: line,
                    column: column,
                    expr: Expression::Block(try!(self.continue_block_stmt())),
                }
            },
            Some(&Token::Keyword(Keyword::If)) => {
                // if expression
                try!(self.match_if_expr())
            },
            Some(&Token::Keyword(Keyword::Fn)) => {
                // function expression
                try!(self.match_fn_expr())
            },
            Some(&Token::Unknown(_)) | Some(&Token::StringLiteral(_)) | Some(&Token::NumberLiteral(_)) | Some(&Token::BooleanLiteral(_)) => {
                // match simple terminals like variable references and literal values
                // FIXME: rustc presently does not have non-lexical lifetimes
                // due to which capturing the value from the token would cause
                // a compile time error here due to the mutable self borrow
                // occuring in the above branches
                // So when rustc gets non-lexical lifetimes, we should update
                // this code to simplify it to what should be obvious
                ExpressionSource {
                    line: line,
                    column: column,
                    expr: match self.lexer.next().map(extract_token) {
                        Some(Token::Unknown(tok)) => {
                            Expression::Reference(tok)
                        },
                        Some(Token::StringLiteral(tok)) => {
                            Expression::StringLiteral(tok)
                        },
                        Some(Token::NumberLiteral(tok)) => {
                            Expression::NumberLiteral(tok)
                        },
                        Some(Token::BooleanLiteral(tok)) => {
                            Expression::BooleanLiteral(tok)
                        },
                        _ => {
                            // since we just verified in the peak method above that this is a literal
                            // value, next will only return a literal value. hence this is unreachable
                            unreachable!();
                        },
                    }
                }
            },
            Some(_) => {
                // if we can't match a terminal, then this is not a valid expression!
                // unwrap is safe here since we just verified via peek that a value is present
                return Err(SyntaxError {
                    line: line,
                    column: column,
                    msg: format!("Unexpected token {}. Expecting start of expression :/", self.lexer.next().map(extract_token).unwrap()),
                });
            },
            None => {
                // we don't match anything like an "empty" expression - hence we error out
                return Err(SyntaxError {
                    line: line,
                    column: column,
                    msg: "Unexpected end of input. I was expecting an expression!".to_string(),
                });
            },
        };
        // now that we have a terminal to operate on, we check if a compound expression could be
        // created. this is done by matching against the lookahead retrieved via peek.
        // if no valid lookahead is found, we return the current expr as it is leaving the token
        // stream untouched.
        // whenever a compound expression is possible, we switch the current expression to the
        // compound one. however, that doesn't terminate parsing. there might be a compound
        // expression *over* the current compound expression. hence, we loop until we can't match
        // a compound expression anymore. when we can't match, we terminate and return the current
        // value of expr
        loop {
            let (line, column) = current_location!(self);
            match self.lexer.peek().map(extract_token_ref) {
                Some(&Token::Punctuator('(')) => {
                    self.lexer.next(); // consume punctuator
                    // call expression
                    let mut args: Vec<ExpressionSource> = vec![];
                    loop {
                        if let Some(&Token::Punctuator(')')) = self.lexer.peek().map(extract_token_ref) {
                            self.lexer.next();
                            break;
                        }
                        if let Some(&Token::Punctuator(',')) = self.lexer.peek().map(extract_token_ref) {
                            self.lexer.next();
                            continue;
                        }
                        args.push(try!(self.match_expression()));
                    }
                    expr = ExpressionSource {
                        line: line,
                        column: column,
                        expr: Expression::Call {
                            callee: Box::new(expr),
                            args: args,
                        },
                    };
                },
                Some(&Token::Punctuator('=')) => {
                    self.lexer.next(); // consume punctuator
                    // either equality check or assignment expression
                    if let Some(&Token::Punctuator('=')) = self.lexer.peek().map(extract_token_ref) {
                        self.lexer.next(); // consume punctuator
                        // double equals == equality check
                        expr = ExpressionSource {
                            line: line,
                            column: column,
                            expr: Expression::Binary {
                                left: Box::new(expr),
                                operator: BinaryOperator::Equals,
                                right: Box::new(try!(self.match_expression())),
                            },
                        };
                    } else {
                        // single equals = assignment
                        if let Expression::Reference(id) = expr.expr { // assignment is only valid for references
                            expr = ExpressionSource {
                                line: line,
                                column: column,
                                expr: Expression::Assignment {
                                    left: id,
                                    right: {
                                        Box::new(try!(self.match_expression()))
                                    },
                                }
                            };
                        } else {
                            return Err(SyntaxError {
                                line: line,
                                column: column,
                                msg: "You can only assign values to references. Assigning to other expressions does not make sense :)".to_string(),
                            });
                        }
                    }
                },
                Some(&Token::Punctuator(ch)) if ch == '+' || ch == '-' || ch == '*' || ch == '/' || ch == '%' || ch == '>' || ch == '<' || ch == '|' || ch == '&' || ch == '!' => {
                    // binary expression
                    // Note that we already covered assignment and binary equality operator above
                    let op = match self.lexer.next().map(extract_token) {
                        Some(Token::Punctuator('+')) => { BinaryOperator::Add },
                        Some(Token::Punctuator('-')) => { BinaryOperator::Subtract },
                        Some(Token::Punctuator('*')) => { BinaryOperator::Multiply },
                        Some(Token::Punctuator('/')) => { BinaryOperator::Divide },
                        Some(Token::Punctuator('%')) => { BinaryOperator::Modulo },
                        Some(Token::Punctuator('>')) => {
                            if let Some(&Token::Punctuator('=')) = self.lexer.peek().map(extract_token_ref) {
                                self.lexer.next();
                                BinaryOperator::GreaterThanOrEqualTo
                            } else {
                                BinaryOperator::GreaterThan
                            }
                        },
                        Some(Token::Punctuator('<')) => {
                            if let Some(&Token::Punctuator('=')) = self.lexer.peek().map(extract_token_ref) {
                                self.lexer.next();
                                BinaryOperator::LessThanOrEqualTo
                            } else {
                                BinaryOperator::LessThan
                            }
                        },
                        Some(Token::Punctuator('|')) => {
                            expect_and_consume_token!(self, Token::Punctuator('|'), "Surely you meant to use the || (logical or) operator? Because orn has no bitwise or."); // completes || (or)
                            BinaryOperator::Or
                        },
                        Some(Token::Punctuator('&')) => {
                            expect_and_consume_token!(self, Token::Punctuator('&'), "Surely you meant to use the && (logical and) operator? Because orn has no bitwise and."); // completes && (and)
                            BinaryOperator::And
                        },
                        Some(Token::Punctuator('!')) => {
                            expect_and_consume_token!(self, Token::Punctuator('='), "Negation is a unary operator. After an expression, != forms the unequality operator!");
                            BinaryOperator::Unequals
                        },
                        _ => { unreachable!(); }
                    };
                    expr = ExpressionSource {
                        line: line,
                        column: column,
                        expr: Expression::Binary {
                            left: Box::new(expr),
                            operator: op,
                            right: Box::new(try!(self.match_expression())),
                        },
                    };
                },
                _ => {
                    return Ok(expr);
                },
            }
        }
    }

    fn advance_from_idle_state(&mut self) -> Result<Option<Statement>, SyntaxError> {
        let stmt = match self.lexer.peek().map(extract_token_ref) {
            Some(&Token::Keyword(Keyword::Let)) => {
                try!(self.match_let_stmt())
            },
            // when in idle state, we always interpret functions and conditionals
            // as statements/declarations and not expressions
            Some(&Token::Keyword(Keyword::Fn)) => {
                Statement::ExpressionStatement(try!(self.match_fn_expr()))
            },
            Some(&Token::Keyword(Keyword::If)) => {
                Statement::ExpressionStatement(try!(self.match_if_expr()))
            },
            Some(&Token::Punctuator('@')) => {
                // TODO: take a flag as a parameter to check if we are matching in function scope,
                // in which case we do not allow rules, and bail out at parse time
                self.lexer.next();
                try!(self.continue_rule())
            },
            Some(&Token::Punctuator(';')) => {
                self.lexer.next().map(extract_token);
                Statement::Empty
            },
            Some(_) => {
                Statement::ExpressionStatement(try!(self.match_expression()))
            },
            None => {
                return Ok(None);
            },
        };
        if let Some(&Token::Punctuator(';')) = self.lexer.peek().map(extract_token_ref) {
            self.lexer.next();
        }
        Ok(Some(stmt))
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = Result<Statement, SyntaxError>;
    fn next(&mut self) -> Option<Result<Statement, SyntaxError>> {
        match self.advance_from_idle_state() {
            Ok(Some(t)) => { Some(Ok(t)) },
            Ok(None) => { None },
            Err(e) => { Some(Err(e)) },
        }
    }
}
