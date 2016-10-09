mod parser;
mod lexer;
mod vm;

use std::process;
use std::env;
use std::path::Path;
use std::io::prelude::*;
use std::fs::File;
use parser::Parser;
use vm::Stack;

fn main() {
    // get arguments
    let args: Vec<_> = env::args().collect();

    // if second arg was not passed
    if args.len() < 2 {
        // print information about us :D :D
        println!(
"
  orn - The swiss army knife of every shell scripter!
        Made in and for 2016 and beyond.

  Author
      Awal Garg <awalgarg@gmail.com>
  
  Source upstream
      <https://github.com/awalGarg/orn>
  
  Documentation
      <https://github.com/awalGarg/orn/wiki>
  
  Version
      0.0.1
  
  Usage
      orn path/to/code.orn
  
  Notes
    Please report issues/bugs/feature requests or send patches on Github
    or send me an email. Just saying hi is also a valid contribution.
    Thank you for trying orn!
"
        );
        
        // and do a successful exit
        process::exit(0);
    }

    // else try opening the file
    let file = &args[1];
    let mut f = match File::open(file.clone()) {
        Ok(f) => { f }, // yay!
        Err(e) => { // nay :(
            println!("An error occurred while trying to open file \"{}\"!", file);
            println!("{}", e);
            process::exit(1);
        },
    };

    // buffer for storing file contents
    let mut s = String::new();
    match f.read_to_string(&mut s) {
        Ok(_) => {},
        Err(e) => { // they probably passed a directory instead of file :|
            println!("An error occurred while reading from path \"{}\"!", file);
            println!("{}", e);
            process::exit(1);
        },
    }

    // get just filename from path for showing in errors
    let filename = Path::new(file)
                    .file_name()
                    .map(|osstr| osstr.to_str().unwrap_or(file))
                    .unwrap_or(file);

    // create parse stream
    let p = Parser::new(&s);

    // create environment to execute code in
    let mut stack = Stack::new();

    // start parsing!
    for stmt in p {
        match stmt {
            Ok(stmt) => {
                // evaluate as they come!
                match stack.eval_stmt(&stmt) {
                    Ok(_) => { /* hurray! */ },
                    Err(o) => {
                        // bad user :(
                        // prints the error which occured
                        println!("{}:{}:{} {}: {}", filename, o.line, o.column, o.error_type, o.msg);

                        // and stack trace which took us so far
                        for (line, column, func) in stack.call_stack {
                            println!("{}:{}:{} at function {}", filename, line, column, func);
                        }
                        
                        // and exit with a failure status code
                        process::exit(1);
                    },
                }
            },
            Err(o) => {
                // why people no write code properly :(
                println!("{}:{}:{} SyntaxError: {}", filename, o.line, o.column, o.msg);
                process::exit(1);
            }
        }
    }
}
