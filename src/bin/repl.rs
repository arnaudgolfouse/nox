use nox2::{
    vm::{VMError, VM},
    Continue,
};
use rustyline::{error::ReadlineError, Editor};
use std::io::{self, Write};

struct Repl {
    current_phrase: String,
    vm: VM,
    editor: Editor<()>,
}

impl Repl {
    fn new() -> Self {
        let vm = VM::new();
        //vm.import_all(libraries::prelude()).unwrap();
        Self {
            current_phrase: String::new(),
            vm,
            editor: Editor::new(),
        }
    }

    fn evaluate(&mut self) -> Result<(), VMError> {
        self.vm.parse_top_level(self.current_phrase.as_str())?;
        println!("=> {}", self.vm.run()?);
        Ok(())
    }

    fn prompt(&mut self) -> bool {
        io::stdout().flush().unwrap();
        let prompt = if self.current_phrase.is_empty() {
            "> "
        } else {
            "    "
        };
        let input = match self.editor.readline(prompt) {
            Ok(input) => input,
            Err(ReadlineError::Eof) | Err(ReadlineError::Interrupted) => return false,
            Err(err) => panic!("{}", err),
        };
        self.current_phrase.push_str(&input); // skip \n
        match self.evaluate() {
            Ok(_) => {
                let mut new_phrase = String::new();
                std::mem::swap(&mut new_phrase, &mut self.current_phrase);
                self.editor.add_history_entry(new_phrase);
            }
            Err(err) => match err.continuable() {
                Continue::Stop => {
                    println!("{}\n", err);
                    let mut new_phrase = String::new();
                    std::mem::swap(&mut new_phrase, &mut self.current_phrase);
                    self.editor.add_history_entry(new_phrase);
                }
                Continue::ContinueWithNewline => self.current_phrase.push('\n'),
                Continue::ContinueWithSpace => self.current_phrase.push(' '),
                Continue::Continue => {}
            },
        }
        true
    }
}

fn main() {
    let mut top_level = Repl::new();
    while top_level.prompt() {}
}
