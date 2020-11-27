use colored::{ColoredString, Colorize};
use std::{fmt, iter::Enumerate, ops::Range, str::Lines};

/// Describe what should the REPL do with this error.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Continue {
    /// Continue on a new line
    Continue,
    /// Hard error, stop
    Stop,
}

/// Helper function, return the width (in characters) of a number
fn int_width(i: usize) -> usize {
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
    range: Range<usize>,
    source: &str,
    source_name: &str,
    warning: bool,
    formatter: &mut fmt::Formatter,
) -> Result<(), fmt::Error> {
    display_error_internal(range, source, source_name, warning, formatter)?;
    writeln!(formatter)?;
    write!(
        formatter,
        "{} : ",
        if warning {
            "warning".yellow().bold()
        } else {
            "error".red().bold()
        }
    )?;
    write!(formatter, "{}", message)?;
    if let Some(note) = note {
        writeln!(formatter)?;
        writeln!(formatter)?;
        write!(formatter, "{} : {}", "note".blue().bold(), note)
    } else {
        Ok(())
    }
}

/// Avoid code duplication
fn display_error_internal(
    range: Range<usize>,
    source: &str,
    source_name: &str,
    warning: bool,
    formatter: &mut fmt::Formatter,
) -> Result<(), fmt::Error> {
    let mut lines = LinesRange::new(source, range).peekable();
    let (line, line_index, line_cols) = lines.next().unwrap_or_default();
    writeln!(formatter, "{}: {}", source_name, line_index)?;

    let multiline = lines.peek().is_some();
    // take two more chars just in case, because we don't know the index of the last line yet.
    let number_width = int_width(line_index + 1) + 2;

    if multiline {
        // first line
        {
            print_numbered_line(formatter, line, line_index, number_width, None, warning)?;
            print_underline(
                formatter,
                number_width + 3,
                None,
                0..line_cols.start,
                '_',
                '^',
                warning,
            )?
        }

        while let Some((line, line_index, line_cols)) = lines.next() {
            if lines.peek().is_some() {
                // middle lines
                print_numbered_line(
                    formatter,
                    line,
                    line_index,
                    number_width,
                    Some("| "),
                    warning,
                )?
            } else {
                // last line
                print_numbered_line(
                    formatter,
                    line,
                    line_index,
                    number_width,
                    Some("| "),
                    warning,
                )?;
                print_underline(
                    formatter,
                    number_width + 3,
                    Some("|_"),
                    0..line_cols.end,
                    '_',
                    '^',
                    warning,
                )?;
            }
        }
    } else {
        print_numbered_line(formatter, line, line_index, number_width, None, warning)?;
        print_underline(
            formatter,
            number_width + 3,
            None,
            line_cols,
            '^',
            '^',
            warning,
        )?
    }

    Ok(())
}

///
/// It returns the line, the line number, and the span covered by the range
/// inside this line.
struct LinesRange<'source> {
    lines: Enumerate<Lines<'source>>,
    start_ptr: *const u8,
    end_ptr: *const u8,
    /// We want to return at least one line, even if the range is out of bounds.
    at_least_one_line: bool,
}

impl<'source> LinesRange<'source> {
    fn new(source: &'source str, range: Range<usize>) -> Self {
        Self {
            lines: source.lines().enumerate(),
            start_ptr: (source.as_ptr() as usize + range.start) as *const u8,
            end_ptr: (source.as_ptr() as usize + range.end) as *const u8,
            at_least_one_line: false,
        }
    }
}

impl<'source> Iterator for LinesRange<'source> {
    type Item = (&'source str, usize, Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        let (mut index, mut next_line) = self.lines.next()?;
        while (next_line.as_ptr() as usize + next_line.len()) <= (self.start_ptr as usize) {
            let (tmp_index, tmp_next_line) = match self.lines.next() {
                Some((index, line)) => (index, line),
                // wait ! check that we already returned at least one line !
                None => {
                    return if !self.at_least_one_line {
                        self.at_least_one_line = true;
                        let columns_range = (self.start_ptr as usize)
                            .saturating_sub(next_line.as_ptr() as usize)
                            ..(self.end_ptr as usize).saturating_sub(next_line.as_ptr() as usize);
                        Some((next_line, index, columns_range))
                    } else {
                        None
                    }
                }
            };
            index = tmp_index;
            next_line = tmp_next_line;
        }
        let next_line_ptr = next_line.as_ptr() as usize;
        let columns_range = (self.start_ptr as usize).saturating_sub(next_line_ptr)
            ..(self.end_ptr as usize).saturating_sub(next_line_ptr);
        if next_line_ptr > (self.end_ptr as usize) {
            if !self.at_least_one_line {
                self.at_least_one_line = true;
                Some((next_line, index, columns_range))
            } else {
                None
            }
        } else {
            self.at_least_one_line = true;
            Some((next_line, index, columns_range))
        }
    }
}

/// Color a string based on warning (yellow) or error (red).
fn color(string: &str, warning: bool) -> ColoredString {
    if warning {
        string.yellow()
    } else {
        string.red()
    }
}

/// Print an underline, and a newline
///
/// # Example
///
/// ```compile_fail
/// print_underline(formatter, 3, 2..4, '_', '^', false)
/// ```
/// produces
/// ```text
/// "     _^"
/// ```
fn print_underline(
    formatter: &mut fmt::Formatter,
    offset: usize,
    prefix: Option<&str>,
    mut range: Range<usize>,
    character: char,
    last_char: char,
    warning: bool,
) -> fmt::Result {
    if range.start == range.end {
        range.end += 1
    }
    let start = offset + range.start;
    let length = range.end.saturating_sub(range.start);
    let mut underline = if let Some(prefix) = prefix {
        prefix.to_owned()
    } else {
        String::new()
    };
    for _ in 0..length.saturating_sub(1) {
        underline.push(character)
    }
    if length != 0 {
        underline.push(last_char)
    }
    writeln!(
        formatter,
        "{underline:>start$}",
        start = start + underline.len(),
        underline = color(&underline, warning)
    )
}

/// Print the line number (colored), the eventual prefix (colored), the line,
/// and a newline.
fn print_numbered_line(
    formatter: &mut fmt::Formatter,
    line: &str,
    line_number: usize,
    number_width: usize,
    prefix: Option<&str>,
    warning: bool,
) -> fmt::Result {
    let colored_number = color(
        &format!(
            "{line:>width$} | ",
            line = line_number + 1, // text usually start at line 1
            width = number_width
        ),
        warning,
    );
    write!(formatter, "{}", colored_number)?;
    if let Some(prefix) = prefix {
        write!(formatter, "{}", color(prefix, warning))?
    }
    writeln!(formatter, "{}", line)
}
