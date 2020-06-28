use crate::{Range, Source};
use colored::Colorize;
use std::{
    cmp::max,
    fmt,
    io::{BufRead, BufReader},
};

/// Describe what should the REPL do with this error.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Continue {
    /// Continue as if we were on the same line
    Continue,
    /// Continue on a new line
    ContinueWithNewline,
    /// Hard error, stop
    Stop,
}

/// Helper function, return the width (in characters) of a number
fn int_width(i: u32) -> usize {
    let mut len = 0;
    for _ in format!("{}", i).chars() {
        len += 1
    }
    len
}

/// Write an error nicely on the given formatter.
///
/// This is used by the various error in this library.
///
/// # Example
///
/// ```should_fail
/// # use nox2::{Error, lexer::Lexer};
/// let mut lexer = Lexer::top_level("1.0.2"); // malformed number
/// lexer.next().unwrap();
/// ```
///
/// Will output :
/// ```text
/// top-level: 1:3
/// 1 | 1.0.2
///        ^
///
/// error : unexpected dot
/// ```
pub fn display_error<F: Fn(&mut fmt::Formatter) -> Result<(), fmt::Error>>(
    display_message: F,
    range: Range,
    source: &Source,
    formatter: &mut fmt::Formatter,
) -> Result<(), fmt::Error> {
    display_error_internal(range, source, formatter)?;
    display_message(formatter)
}

/// Avoids code duplication
fn display_error_internal(
    range: Range,
    source: &Source,
    formatter: &mut fmt::Formatter,
) -> Result<(), fmt::Error> {
    /// helper function to print a line with its number (and and optional error trail)
    fn print_line(
        formatter: &mut fmt::Formatter,
        line: String,
        line_number: usize,
        number_width: usize,
        error_trail: bool,
    ) -> Result<(), fmt::Error> {
        formatter.write_str(
            &format!(
                "{line:<width$} | ",
                line = line_number + 1, // text usually start at line 1
                width = number_width
            )
            .red(),
        )?;
        if error_trail {
            formatter.write_str(&"| ".red())?
        }
        for c in line.chars() {
            if c == '\t' {
                // tab as 4 spaces
                formatter.write_str("    ")?
            } else {
                write!(formatter, "{}", c)?
            }
        }
        writeln!(formatter)
    }

    /// helper function to print a line with its number (and and optional error trail), as well
    /// as creating an underline of '^' between the specified bounds (`error_start` and
    /// `error_end`).
    fn print_line_underlined(
        formatter: &mut fmt::Formatter,
        line: String,
        line_number: usize,
        number_width: usize,
        error_trail: bool,
        error_start: usize,
        error_end: usize,
    ) -> Result<String, fmt::Error> {
        write!(
            formatter,
            "{}",
            &format!(
                "{line:<width$} | ",
                line = line_number + 1, // text usually start at line 1
                width = number_width
            )
            .red()
        )?;
        let mut underline = format!("{1:0$} {2} ", number_width, "", " ".red());
        if error_trail {
            write!(formatter, "{}", "| ".red())?;
            underline.push_str(&format!("{}, ", "|_".red()))
        }
        for (i, c) in line.chars().enumerate() {
            if c == '\t' {
                // tab as 4 spaces
                formatter.write_str("    ")?;
                if i < error_end && i >= error_start {
                    underline.push_str(&"____".red())
                } else if i < error_start {
                    underline.push_str("    ")
                }
            } else {
                write!(formatter, "{}", c)?;
                if i < error_end && i >= error_start {
                    underline.push_str(&"_".red())
                } else if i < error_start {
                    underline.push(' ')
                }
            }
            if i == error_end {
                underline.push_str(&"^".red())
            }
        }
        writeln!(formatter)?;
        Ok(underline)
    }

    writeln!(
        formatter,
        "{}: {}:{}",
        source.name(),
        range.start.line + 1,
        range.start.column
    )?;

    let multiline = range.start.line < range.end.line;
    let number_width = max(
        int_width(range.start.line + 1),
        int_width(range.end.line + 1),
    );
    let reader = BufReader::new(source.content().as_bytes());

    if multiline {
        let mut lines = reader
            .lines()
            .enumerate()
            .skip(range.start.line as usize)
            .take((range.end.line - range.start.line + 1) as usize);

        // first line
        {
            let (i, first_line) = lines.next().unwrap();
            let underline = print_line_underlined(
                formatter,
                first_line.unwrap(),
                i,
                number_width,
                false,
                0,
                range.start.column.saturating_sub(1) as usize,
            )?;
            writeln!(formatter, "{}", underline)?
        }

        // middle lines
        let underline = loop {
            let (i, line) = match lines.next() {
                Some((i, line)) => {
                    if i == range.end.line as usize {
                        break print_line_underlined(
                            formatter,
                            line.unwrap(),
                            i,
                            number_width,
                            true,
                            0,
                            range.end.column as usize,
                        )?;
                    }
                    (i, line.unwrap())
                }
                None => unreachable!(),
            };
            print_line(formatter, line, i, number_width, true)?
        };

        // last line
        writeln!(formatter, "{}", underline)?;
    } else {
        let line_number = range.start.line as usize;
        let line = reader.lines().nth(line_number).unwrap().unwrap();
        let underline = print_line_underlined(
            formatter,
            line,
            line_number,
            number_width,
            false,
            range.start.column as usize,
            range.end.column as usize,
        )?
        .replace("_", "^");
        writeln!(formatter, "{}", underline.red())?
    }

    writeln!(formatter)?;
    write!(formatter, "{} : ", "error".red().bold())
}
