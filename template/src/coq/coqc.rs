//! Support for running Coq files and capturing output.

use std::{
    fs,
    hash::{DefaultHasher, Hash, Hasher},
    io::ErrorKind,
    path::Path,
    process::{Command, Stdio},
};

use anyhow::{bail, Context as _};
use tempdir::TempDir;

use super::parse::last_sentence_span;

/// A Coq file that uses Redirect commands to gather outputs.
///
/// A [`CoqFile`] can be run to gather its outputs, and they can be cached based
/// on the file contents to speed up repeated compilations.
///
/// A literate Coq file is used to generate such a file programmatically (though
/// that code is not in this module).
#[derive(Debug, Clone)]
pub struct CoqFile {
    contents: String,
    output_names: Vec<String>,
    contents_hash: DefaultHasher,
}

impl Hash for CoqFile {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.contents.hash(state);
    }
}

impl Default for CoqFile {
    fn default() -> Self {
        Self::new()
    }
}

impl CoqFile {
    /// Create an empty file suitable for building incrementally.
    pub fn new() -> Self {
        Self {
            contents: String::new(),
            output_names: vec![],
            contents_hash: DefaultHasher::new(),
        }
    }

    /// A short hash of the contents so far, to make output files unique
    /// (between different files) and deterministic.
    fn short_hash(&self) -> String {
        format!("{:016x}", self.contents_hash.finish())[..10].to_string()
    }

    pub fn push_str(&mut self, s: &str) {
        self.contents.push_str(s);
        s.hash(&mut self.contents_hash);
    }

    /// Add text before the last sentence in the file.
    pub fn push_before_last_sentence(&mut self, s: &str) {
        let (sentence_start, _) =
            last_sentence_span(&self.contents).expect("could not find sentence to add to");
        self.contents.insert_str(sentence_start, s);
        // this isn't actually the hash of the contents, but it should incorporate all the relevant info
        sentence_start.hash(&mut self.contents_hash);
        s.hash(&mut self.contents_hash);
    }

    /// Remove the last sentence from the file and return it.
    ///
    /// The returned output includes any text after the last sentence (for
    /// example, whitespace).
    pub fn remove_sentence(&mut self) -> String {
        let (start, _) = last_sentence_span(&self.contents).unwrap();
        let sentence = self.contents[start..].to_string();
        self.contents.truncate(start);
        start.hash(&mut self.contents_hash);
        sentence
    }

    /// Add a Redirect command around the last sentence to capture its output
    /// when the file is run.
    pub fn add_output(&mut self, prefix: &str) {
        let output_i = self.output_names.len();
        let output_name = format!("{prefix}_{hash}_{output_i}", hash = self.short_hash());
        self.push_before_last_sentence(&format!("Redirect \"{output_name}\" "));
        self.output_names.push(output_name);
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }
}

#[derive(Debug, Clone)]
pub struct CoqArgs {
    coq_args: Vec<String>,
}

/// CoqConfig represents a configuration for running Coq files.
///
/// It serves to abstract over running coqc directly from `CoqArgs` vs running
/// it through a cache with [`super::cache::CoqOutputCache`].
pub trait CoqConfig {
    /// Run coq to compile `file` and gather its outputs, returning the outputs.
    fn get_outputs(&self, file: &CoqFile) -> Result<Vec<String>, anyhow::Error>;
}

impl Default for CoqArgs {
    fn default() -> Self {
        Self::new()
    }
}

impl CoqArgs {
    fn from_rocqproject_contents(contents: &str) -> Result<Self, anyhow::Error> {
        let mut coq_args = vec![];
        for line in contents.lines() {
            // strip comments
            let line = line.find("#").map_or(line, |i| &line[..i]);
            let Ok(args) = shell_words::split(line) else {
                continue;
            };
            let args = args
                .into_iter()
                .map(|s| s.replace("\'", ""))
                .collect::<Vec<_>>();
            let mut args: &[String] = &args;
            while !args.is_empty() {
                if args.len() >= 2 && args[0] == "-arg" {
                    coq_args.push(args[1].to_string());
                    args = &args[2..];
                } else if args.len() >= 3 && (args[0] == "-Q" || args[0] == "-R") {
                    coq_args.extend(args[..3].iter().map(|s| s.to_string()));
                    args = &args[3..];
                } else {
                    // something unknown, skip it (supports file names in _RocqProject)
                    args = &args[1..];
                }
            }
        }
        Ok(Self { coq_args })
    }

    pub fn from_rocqproject(path: &Path) -> Result<Self, anyhow::Error> {
        let contents = fs::read_to_string(path)
            .with_context(|| format!("could not read file {}", path.to_string_lossy()))?;
        Self::from_rocqproject_contents(&contents)
    }

    pub fn new() -> Self {
        Self { coq_args: vec![] }
    }

    pub fn extend_args(&mut self, args: &[String]) {
        self.coq_args.extend_from_slice(args);
    }

    fn run_coqc(&self, path: &Path) -> Result<(), anyhow::Error> {
        let r = Command::new("rocq")
            .arg("compile")
            .args(&self.coq_args)
            .arg("-noglob")
            .args(["-output-directory", "."])
            .arg(path)
            .status();
        match r {
            Ok(s) if s.success() => Ok(()),
            Ok(s) => bail!("rocq compile failed with exit code {}", s.code().unwrap()),
            Err(err) => {
                if err.kind() == ErrorKind::NotFound {
                    bail!("could not find rocq in PATH");
                }
                return Err(err).with_context(|| "rocq failed");
            }
        }
    }

    fn run_coqc_contents(&self, contents: &str) -> Result<(), anyhow::Error> {
        let tmp_dir = TempDir::new("coq").with_context(|| "could not create temp dir")?;
        // NOTE: the current module's name is taken from this input file and is
        // technically visible: using [Locate] on a definition will show this
        // path, and it can be used for fully qualified names. This isn't
        // commonly used. In any case using a temporary directory makes the rest
        // of the module path mismatch the input as well.
        let file_path = tmp_dir.path().join("__input.v");
        fs::write(&file_path, contents).with_context(|| "could not write temp Coq file")?;
        self.run_coqc(&file_path)?;
        // Temporary directory is deleted when it goes out of scope,
        // automatically deleting the input and build outputs.
        Ok(())
    }
}

impl CoqConfig for CoqArgs {
    fn get_outputs(&self, file: &CoqFile) -> Result<Vec<String>, anyhow::Error> {
        self.run_coqc_contents(&file.contents)?;

        let mut outputs = vec![];
        for output_name in file.output_names.iter() {
            let output_path = format!("{output_name}.out");
            let output = fs::read_to_string(&output_path)
                .with_context(|| format!("could not read Coq output file {output_path}.out"))?;
            outputs.push(output);
            fs::remove_file(&output_path)?;
        }

        Ok(outputs)
    }
}

/// Convenience for checking of rocq is available on the $PATH.
pub fn is_rocq_available() -> bool {
    Command::new("rocq")
        .arg("--print-version")
        .stdout(Stdio::null())
        .status()
        .is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// make sure this doesn't panic
    #[test]
    fn test_is_rocq_available() {
        _ = is_rocq_available();
    }

    #[test]
    fn test_rocqproject_parsing() {
        let s = r#"
-Q src/sys_verif sys_verif
-arg -w -arg -ssr-search-moved
-arg -w -arg +deprecated-instance-without-locality
# -arg -w -arg +all

-arg -set -arg "'Extraction Output Directory=src/software_foundations/'" # tricky argument separation

# parsing should ignore file names
src/software_foundations/Basics.v
      "#;
        let cfg = CoqArgs::from_rocqproject_contents(s).unwrap();
        assert_eq!(
            &cfg.coq_args,
            &[
                "-Q",
                "src/sys_verif",
                "sys_verif",
                "-w",
                "-ssr-search-moved",
                "-w",
                "+deprecated-instance-without-locality",
                "-set",
                "Extraction Output Directory=src/software_foundations/",
            ]
        );
    }
}
