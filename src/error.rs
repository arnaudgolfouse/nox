use crate::Range;
use colored::Colorize;
use std::{
    cmp::max,
    fmt,
    io::{BufRead, BufReader},
};

/// Describe what should the REPL do with this error.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Continue {
    /// Continue on a new line
    Continue,
    /// Hard error, stop
    Stop,
}

/// Helper function, return the width (in characters) of a number
fn int_width(i: u32) -> usize {
    format!("{}", i).chars().count()
}

/// Write an error nicely on the given formatter.
///
/// This is used by the various error in this library.
///
/// # Example
///
/// ```compile_fail
/// let mut lexer = Lexer::top_level("1.0.2"); // malformed number
/// lexer.next().unwrap();
/// ```
///
/// Will output :
/// ```text
/// top-level: 1:4
/// 1 | 1.0.2
///        ^
///
/// error : unexpected dot
/// ```
pub(crate) fn display_error<T: fmt::Display, U: fmt::Display>(
    message: T,
    note: Option<U>,
    range: Range,
    source: &str,
    source_name: &str,
    warning: bool,
    formatter: &mut fmt::Formatter,
) -> Result<(), fmt::Error> {
    display_error_internal(range, source, source_name, warning, formatter)?;
    write!(formatter, "{}", message)?;
    if let Some(note) = note {
        writeln!(formatter)?;
        writeln!(formatter)?;
        write!(formatter, "{} : {}", "note".blue().bold(), note)
    } else {
        Ok(())
    }
}

/// Avoids code duplication
fn display_error_internal(
    range: Range,
    source: &str,
    source_name: &str,
    warning: bool,
    formatter: &mut fmt::Formatter,
) -> Result<(), fmt::Error> {
    let color = |x| {
        if warning {
            <&str>::yellow(x)
        } else {
            <&str>::red(x)
        }
    };
    let color_str = |x: String| {
        if warning {
            <&str>::yellow(&x)
        } else {
            <&str>::red(&x)
        }
    };

    // helper function to print a line with its number (and and optional error trail)
    let print_line = |formatter: &mut fmt::Formatter,
                      line: String,
                      line_number: usize,
                      number_width: usize,
                      error_trail: bool|
     -> Result<(), fmt::Error> {
        write!(
            formatter,
            "{}",
            if warning {
                format!(
                    "{line:<width$} | ",
                    line = line_number + 1, // text usually start at line 1
                    width = number_width
                )
                .yellow()
            } else {
                format!(
                    "{line:<width$} | ",
                    line = line_number + 1, // text usually start at line 1
                    width = number_width
                )
                .red()
            }
        )?;
        if error_trail {
            write!(formatter, "{} ", color("|"))?;
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
    };

    // helper function to print a line with its number (and and optional error trail), as well
    // as creating an underline of '^' between the specified bounds (`error_start` and
    // `error_end`).
    let print_line_underlined = |formatter: &mut fmt::Formatter,
                                 line: String,
                                 line_number: usize,
                                 number_width: usize,
                                 error_trail: bool,
                                 error_start: usize,
                                 error_end: usize|
     -> Result<String, fmt::Error> {
        write!(
            formatter,
            "{}",
            if warning {
                format!(
                    "{line:<width$} | ",
                    line = line_number + 1, // text usually start at line 1
                    width = number_width
                )
                .yellow()
            } else {
                format!(
                    "{line:<width$} | ",
                    line = line_number + 1, // text usually start at line 1
                    width = number_width
                )
                .red()
            }
        )?;
        let mut underline = format!("{1:0$}   ", number_width, "");
        if error_trail {
            write!(formatter, "{}", color("| "))?;
            underline.push_str("|_")
        }
        let mut column_max = 0;
        for (i, c) in line.chars().enumerate() {
            column_max += 1;
            if c == '\t' {
                // tab as 4 spaces
                formatter.write_str("    ")?;
                if i < error_end && i >= error_start {
                    underline.push_str("____")
                } else if i < error_start {
                    underline.push_str("    ")
                }
            } else {
                write!(formatter, "{}", c)?;
                if i < error_end && i >= error_start {
                    underline.push('_')
                } else if i < error_start {
                    underline.push(' ')
                }
            }
            if i == error_end {
                underline.push('^')
            }
        }
        while error_end > column_max {
            column_max += 1;
            underline.push('_')
        }
        if error_end == column_max {
            underline.push('^')
        }
        writeln!(formatter)?;
        Ok(color_str(underline).to_string())
    };

    writeln!(
        formatter,
        "{}: {}:{}",
        source_name,
        range.start.line + 1,
        range.start.column + 1
    )?;

    let multiline = range.start.line < range.end.line;
    let number_width = max(
        int_width(range.start.line + 1),
        int_width(range.end.line + 1),
    );
    let reader = BufReader::new(source.as_bytes());

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
        writeln!(
            formatter,
            "{}",
            if warning {
                underline.yellow()
            } else {
                underline.red()
            }
        )?
    }

    writeln!(formatter)?;
    write!(
        formatter,
        "{} : ",
        if warning {
            "warning".yellow().bold()
        } else {
            "error".red().bold()
        }
    )
}
