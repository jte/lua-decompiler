/// Pass 6 – Dead-code elimination.
///
/// Removes patterns that are provably no-ops in the output:
///   • Empty generic-for loops  (`for … do\nend`)
///   • Empty numeric-for loops
///   • Empty if blocks           (`if … then\nend`)
///   • `local _NAME = nil`

pub fn run(src: &str) -> String {
    let lines: Vec<&str> = src.lines().collect();
    let mut out: Vec<&str> = Vec::with_capacity(lines.len());
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim();

        // Empty for … do / end pair
        if (trimmed.starts_with("for ") || trimmed.starts_with("for\t"))
            && trimmed.ends_with("do")
        {
            if let Some(next) = lines.get(i + 1) {
                if next.trim() == "end" {
                    i += 2;
                    continue;
                }
            }
        }

        // Empty if … then / end pair
        if trimmed.starts_with("if ") && trimmed.ends_with("then") {
            if let Some(next) = lines.get(i + 1) {
                if next.trim() == "end" {
                    i += 2;
                    continue;
                }
            }
        }

        // local _NAME = nil  (dead initialisation)
        if trimmed.starts_with("local _") && trimmed.ends_with("= nil") {
            i += 1;
            continue;
        }

        out.push(line);
        i += 1;
    }

    out.join("\n")
}
