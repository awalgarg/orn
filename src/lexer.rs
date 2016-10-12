use std::str::Chars;
use std::fmt;

// wrapper for characters
// useful for tracing position of error in source text
struct SourceChar {
    ch: char,
    line: u32,
    column: u32,
}

// simple scanner which can be rewinded by one character only
struct Scanner<'a> {
    source: Chars<'a>,
    line: u32,
    column: u32,
    last_char: char,
    has_rewinded: bool,
}

impl<'a> Scanner<'a> {
    fn new(src: &'a String) -> Scanner<'a> {
        Scanner { source: src.chars(), line: 1, column: 0, last_char: ' ', has_rewinded: false }
    }
    fn rewind(&mut self) {
        // the iterator next method takes this flag into account
        self.has_rewinded = true;
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = SourceChar;
    fn next(&mut self) -> Option<SourceChar> {
        if self.has_rewinded {
            self.has_rewinded = false;
            Some(SourceChar { ch: self.last_char, line: self.line, column: self.column })
        } else {
            let ch = self.source.next();
            match ch {
                Some('\n') => {
                    self.line += 1;
                    self.column = 1;
                    self.last_char = '\n';
                    Some(SourceChar { ch: '\n', line: self.line, column: self.column })
                },
                Some(ch) => {
                    self.column += 1;
                    self.last_char = ch;
                    Some(SourceChar { ch: ch, line: self.line, column: self.column })
                },
                _ => None
            }
        }
    }
}

// tokens are basically source lexemes split by whitespace but more intelligent splitting
// and also assigned with "Tags" in this enum
pub enum Token {
    StringLiteral(String),
    NumberLiteral(String), // the exact number type is known later in the parse pipeline
    BooleanLiteral(bool),
    Keyword(Keyword),
    Unknown(String),
    Punctuator(char),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Token::StringLiteral(ref s) => {
                write!(f, "\"{}\"", s)
            },
            &Token::NumberLiteral(ref s) => {
                write!(f, "{}", s)
            },
            &Token::BooleanLiteral(ref b) => {
                write!(f, "{}", b)
            },
            &Token::Keyword(ref k) => {
                write!(f, "{}", k)
            },
            &Token::Unknown(ref s) => {
                write!(f, "{}", s)
            },
            &Token::Punctuator(ref ch) => {
                write!(f, "{}", ch)
            },
        }
    }
}

pub struct Lexeme {
    pub line: u32,
    pub column: u32,
    pub token: Token,
}

pub enum Keyword {
    If,
    Else,
    Fn,
    Let,
    Mut,
    UInt,
    Int,
    Str,
    Float,
    Bool,
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Keyword::If => { write!(f, "if") },
            &Keyword::Else => { write!(f, "else") },
            &Keyword::Fn => { write!(f, "fn") },
            &Keyword::Let => { write!(f, "let") },
            &Keyword::Mut => { write!(f, "mut") },
            &Keyword::UInt => { write!(f, "uint") },
            &Keyword::Int => { write!(f, "int") },
            &Keyword::Str => { write!(f, "str") },
            &Keyword::Float => { write!(f, "float") },
            &Keyword::Bool => { write!(f, "bool") },
        }
    }
}

fn identify_token(token: String) -> Token {
    if token == "if" {
        Token::Keyword(Keyword::If)
    } else if token == "fn" {
        Token::Keyword(Keyword::Fn)
    } else if token == "else" {
        Token::Keyword(Keyword::Else)
    } else if token == "let" {
        Token::Keyword(Keyword::Let)
    } else if token == "mut" {
        Token::Keyword(Keyword::Mut)
    } else if token == "true" {
        Token::BooleanLiteral(true)
    } else if token == "false" {
        Token::BooleanLiteral(false)
    } else if token == "uint" {
        Token::Keyword(Keyword::UInt)
    } else if token == "int" {
        Token::Keyword(Keyword::Int)
    } else if token == "str" {
        Token::Keyword(Keyword::Str)
    } else if token == "float" {
        Token::Keyword(Keyword::Float)
    } else if token == "bool" {
        Token::Keyword(Keyword::Bool)
    } else {
        // the parser/interpreter phase classifies it into a variable
        // or whatever it is
        Token::Unknown(token)
    }
}

// Bunch of states in which the lexer could be (which denotes what it could be consuming)
// So LexerState::Comment means the lexer is presently consuming a comment token
enum LexerState {
    Idle,
    StringLiteral { quote: char },
    NumberLiteral { decimal: u8 }, // decimal holds position of decimal to ensure number is in proper format
    Comment,
    Other,
}

macro_rules! wrap_as_lexeme {
    ($self_:ident, $token:expr) => {
        Lexeme { token: $token, line: $self_.line, column: $self_.column }
    }
}

pub struct Lexer<'a> {
    scanner: Scanner<'a>,
    accepting: LexerState,
    line: u32,
    column: u32,
    buffer: String,
    escape_next: bool,
}
impl<'a> Lexer<'a> {
    pub fn new(src: &'a String) -> Lexer<'a> {
        Lexer {
            scanner: Scanner::new(src),
            accepting: LexerState::Idle,
            buffer: String::new(),
            escape_next: false,
            line: 0,
            column: 0,
        }
    }
    fn dump_buffer(&mut self) -> String {
        let new_buf = self.buffer.clone();
        self.buffer.truncate(0);
        new_buf
    }
}
impl<'a> Iterator for Lexer<'a> {
    type Item = Lexeme;
    fn next(&mut self) -> Option<Lexeme> {
        // this is a state machine, basically
        // takes a character from the scanner and depending on the present state
        // tries to identify what the lexeme type could be
        // then keeps pushing to buffer until a complete lexeme is matched
        // once a match is complete, the buffer is cloned to a lexeme, and the
        // original buffer is truncated to 0 bytes
        // the clone is wrapped in a Token enum type and returned, breaking from
        // the infinite loop
        loop {
            let sch = self.scanner.next();
            match sch {
                Some(SourceChar { ch, line, column }) => {
                    match self.accepting {
                        LexerState::Idle => {
                            self.line = line;
                            self.column = column;
                            if ch == '"' || ch == '\'' {
                                self.accepting = LexerState::StringLiteral { quote: ch };
                            } else if ch.is_digit(10) {
                                // note that '-' does not start a number literal
                                // so -4 in expression context denotes negative of the
                                // number literal 4, hence it is broken into two tokens
                                // Punctuator('-') and NumberLiteral('4')
                                self.accepting = LexerState::NumberLiteral { decimal: 0 };
                                self.buffer.push(ch);
                            } else if ch.is_alphabetic() || ch == '_' {
                                self.accepting = LexerState::Other;
                                self.buffer.push(ch);
                            } else if ch == '@' ||
                                      ch == '(' ||
                                      ch == ')' ||
                                      ch == ']' ||
                                      ch == '[' ||
                                      ch == '}' ||
                                      ch == '{' ||
                                      ch == '+' ||
                                      ch == '-' ||
                                      ch == '*' ||
                                      ch == '/' ||
                                      ch == ':' ||
                                      ch == ';' ||
                                      ch == '=' ||
                                      ch == '.' ||
                                      ch == ',' ||
                                      ch == '!' ||
                                      ch == '~' ||
                                      ch == '<' ||
                                      ch == '>' ||
                                      ch == '^' ||
                                      ch == '%' ||
                                      ch == '|' ||
                                      ch == '&' ||
                                      ch == '$' ||
                                      ch == '`' {
                                return Some(wrap_as_lexeme!(self, Token::Punctuator(ch)));
                            } else if ch == '#' {
                                // note that since the lexer breaks the source into *tokens*
                                // without any semantic verification, comments can only start after
                                // a complete token has been consumed. so the following is
                                // correctly tokenized:
                                // if foo { # bar
                                // the parser simply skips comment tokens so only sees
                                // if foo {
                                // which is the intended behavior
                                self.accepting = LexerState::Comment;
                            } else if !ch.is_whitespace() {
                                // TODO: handle error properly
                                println!("Unknown character {} at line {} column {} encountered", ch, self.line, self.column);
                            }
                        },
                        LexerState::StringLiteral { quote } => {
                            if self.escape_next {
                                // TODO: maybe add a bunch of other escape codes?
                                if ch == 't' {
                                    self.buffer.push('\t');
                                } else if ch == 'n' {
                                    self.buffer.push('\n');
                                } else {
                                    self.buffer.push(ch);
                                }
                                self.escape_next = false;
                            } else {
                                if ch == quote {
                                    self.accepting = LexerState::Idle;
                                    return Some(wrap_as_lexeme!(self, Token::StringLiteral(self.dump_buffer())));
                                } else if ch == '\\' {
                                    self.escape_next = true;
                                } else {
                                    self.buffer.push(ch);
                                }
                            }
                        },
                        LexerState::NumberLiteral { decimal } => {
                            if ch.is_digit(10) {
                                self.buffer.push(ch);
                                // if the last character we saw was a decimal
                                if decimal == 1 {
                                    // then we have succesfully parsed atleast part of a decimal
                                    // number
                                    self.accepting = LexerState::NumberLiteral { decimal: 2 };
                                }
                            } else if ch == '.' {
                                if decimal > 0 { // already seen a decimal!
                                    // in the next iteration, this period will be seen as a punctuator
                                    // forming part of a member expression (1..to_string())
                                    self.scanner.rewind();
                                    self.accepting = LexerState::Idle;
                                    return Some(wrap_as_lexeme!(self, Token::NumberLiteral(self.dump_buffer())));
                                } else {
                                    self.buffer.push(ch);
                                    self.accepting = LexerState::NumberLiteral { decimal: 1 }; // signify that we last saw a decimal
                                }
                            } else {
                                self.scanner.rewind();
                                self.accepting = LexerState::Idle;
                                return Some(wrap_as_lexeme!(self, Token::NumberLiteral(self.dump_buffer())));
                            }
                        },
                        LexerState::Comment => {
                            if ch == '\n' {
                                self.accepting = LexerState::Idle;
                            }
                        },
                        LexerState::Other => {
                            // valid identifier style characters are alphabets, digits and _
                            if ch.is_alphabetic() || ch.is_digit(10) || ch == '_' {
                                self.buffer.push(ch);
                            } else {
                                // if this character is none of those, then it is interpreted as a
                                // break in the lexeme
                                if !ch.is_whitespace() {
                                    // whitespace is ignored, but other characters need rewinding
                                    self.scanner.rewind();
                                }
                                self.accepting = LexerState::Idle;
                                return Some(wrap_as_lexeme!(self, identify_token(self.dump_buffer())));
                            }
                        },
                    }
                },
                None => {
                    match self.accepting {
                        LexerState::Idle => return None, // terminate lexing machine
                        LexerState::StringLiteral { .. } => {
                            // this is kinda odd, but our lexer forgives the ommission of a closing
                            // quote. this is not that big of an issue because a simple string
                            // literal at the end of the file is basically a no-op anyways. in
                            // expression context, the parser will catch this and throw
                            // This is mostly noticeable in a repl, when a user would expect
                            // continuation to catchup and let him enter a multiline string.
                            // We should probably handle that on the repl end though
                            self.accepting = LexerState::Idle;
                            return Some(wrap_as_lexeme!(self, Token::StringLiteral(self.dump_buffer())));
                        },
                        LexerState::NumberLiteral { .. } => {
                            self.accepting = LexerState::Idle;
                            return Some(wrap_as_lexeme!(self, Token::NumberLiteral(self.dump_buffer())));
                        },
                        LexerState::Comment => {
                            self.accepting = LexerState::Idle;
                        },
                        LexerState::Other => {
                            self.accepting = LexerState::Idle;
                            return Some(wrap_as_lexeme!(self, identify_token(self.dump_buffer())));
                        },
                    }
                },
            }
        }
    }
}
