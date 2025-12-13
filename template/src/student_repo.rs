//! Create the student repo (sys-verif-fa26-proofs).
// allow using format! regardless of whether interpolation is needed or not
#![allow(clippy::useless_format)]
use std::fs;
use std::io;
use std::path::Path;

use anyhow::Context as _;

use crate::app::App;

fn copy_dir_all(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> io::Result<()> {
    fs::create_dir_all(&dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(entry.path(), dst.as_ref().join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.as_ref().join(entry.file_name()))?;
        }
    }
    Ok(())
}

/// Copy file src to dst, creating parent directories as necessary (as the
/// `install` command does). If src is a directory, it is recursively copied.
fn install_copy(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> anyhow::Result<()> {
    let src = src.as_ref();
    let dst = dst.as_ref();
    if src.is_dir() {
        fs::create_dir_all(dst)?;
        copy_dir_all(src, dst)
            .with_context(|| format!("could not copy directory {}", src.display()))?;
        return Ok(());
    }
    if let Some(dir) = dst.parent() {
        fs::create_dir_all(dir)?;
    }
    fs::copy(src, dst).with_context(|| format!("could not copy {}", src.display()))?;
    Ok(())
}

fn install_copy_coq(src_dir: impl AsRef<Path>, dst: impl AsRef<Path>) -> io::Result<()> {
    let dst = dst.as_ref();
    for src in walkdir::WalkDir::new(src_dir) {
        let src = src?;
        if src.file_type().is_dir() {
            fs::create_dir_all(dst.join(src.path()))?;
        } else if src.path().extension().is_some_and(|ext| ext == "v") {
            fs::copy(src.path(), dst.join(src.path()))?;
        }
    }
    Ok(())
}

fn create_opam(dst: impl AsRef<Path>) -> io::Result<()> {
    let dst = dst.as_ref();
    let opam_content =
        fs::read_to_string("sys-verif.opam").expect("Failed to read sys-verif.opam file");
    let lines = opam_content.lines().map(|line| {
        let mut line = line.to_string();
        if line.contains("maintainer:") || line.contains("authors:") {
            line = regex::Regex::new(r#""[^"]*""#)
                .unwrap()
                .replace(&line, r#""Student""#)
                .to_string();
        }
        if line.contains("homepage:") || line.contains("bug-reports:") || line.contains("dev-repo")
        {
            line = line.replace(
                "github.com/tchajed/sys-verif-solutions",
                "github.com/tchajed/sys-verif-fa26",
            );
        }
        line
    });

    let updated_opam_content = lines.collect::<Vec<_>>().join("\n");
    fs::write(dst.join("sys-verif.opam"), updated_opam_content)?;
    Ok(())
}

fn copy_static(out: &Path) -> anyhow::Result<()> {
    install_copy("README-student.md", out.join("README.md"))?;
    install_copy(".gitignore-student", out.join(".gitignore"))?;

    let files_to_install = [
        "etc/update-goose.sh",
        "etc/prepare-submit",
        ".devcontainer/",
        ".vscode/",
        // rocq setup
        "Makefile",
        "_RocqProject",
        "src/sys_verif/options.v",
        "src/sys_verif/program_proof/prelude.v",
        "src/sys_verif/program_proof/empty_ffi.v",
        "src/sys_verif/program_proof/functional_init.v",
        "src/sys_verif/program_proof/concurrent_init.v",
        "src/sys_verif/program_proof/heap_init.v",
        // dafny demo
        "dafny/",
    ];
    create_opam(out)?;
    for src in &files_to_install {
        install_copy(src, out.join(src))?;
    }
    Ok(())
}

fn copy_software_foundations(out: &Path) -> anyhow::Result<()> {
    for src in &[
        "src/sys_verif/software_foundations.v",
        // non-Coq files
        "src/software_foundations/LICENSE",
        "src/software_foundations/impdriver.ml",
    ] {
        install_copy(src, out.join(src))?;
    }
    install_copy_coq("src/software_foundations", out)?;
    Ok(())
}

fn copy_go(out: &Path) -> anyhow::Result<()> {
    for src in walkdir::WalkDir::new("go") {
        let src = src?;
        install_copy(src.path(), out.join(src.path()))?;
    }
    install_copy_coq("src/code", out)?;
    install_copy_coq("src/generatedproof", out)?;
    Ok(())
}

fn create_exercise_or_solution(input: &str, out: &Path, solution: bool) -> anyhow::Result<()> {
    fs::create_dir_all(out.parent().unwrap())?;
    App::run(
        if solution { "solution" } else { "exercise" },
        &[input, "--output", &out.to_string_lossy()],
    )?;
    Ok(())
}

/// Compile the Coq template at `input` to an exercise file at `out`.
fn create_exercise(input: &str, out: &Path) -> anyhow::Result<()> {
    create_exercise_or_solution(input, out, false)
}

#[allow(dead_code)]
/// Compile the Coq template at `input` to a solution file at `out`.
fn create_solution(input: &str, out: &Path) -> anyhow::Result<()> {
    create_exercise_or_solution(input, out, true)
}

fn create_assignments(out: &Path) -> anyhow::Result<()> {
    let src_dir = Path::new("src/sys_verif/assignment_solns");
    let dst_dir = out.join("src/sys_verif/assignments");
    for path in walkdir::WalkDir::new(src_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "v"))
    {
        let src_path = path.path();
        let dst_path = dst_dir.join(src_path.strip_prefix(src_dir).unwrap());
        create_exercise(&src_path.to_string_lossy(), &dst_path)?;
    }
    Ok(())
}

fn create_notes(out: &Path) -> anyhow::Result<()> {
    // TODO: start distributing lecture notes as "exercise" code (before the
    // corresponding lecture) and "solution" code after, to not give away
    // answers but then reveal them afterward.

    // Lecture notes
    for path in walkdir::WalkDir::new("src/sys_verif/notes")
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "v"))
    {
        let src_path = path.path().to_string_lossy();
        let dst_path = out.join("src/sys_verif/notes").join(path.file_name());
        create_exercise(&src_path, &dst_path)?;
    }
    // Program proofs guide (demos are handled separately)
    for path in walkdir::WalkDir::new("src/sys_verif/program_proof/guide")
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "v"))
    {
        let src_path = path.path().to_string_lossy();
        let dst_path = out
            .join("src/sys_verif/program_proof/guide")
            .join(path.file_name());
        create_solution(&src_path, &dst_path)?;
    }
    Ok(())
}

fn create_demos(out: &Path) -> anyhow::Result<()> {
    for path in walkdir::WalkDir::new("src/sys_verif/program_proof/demos")
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "v"))
    {
        let src_path = path.path().to_string_lossy();
        let dst_path = out
            .join("src/sys_verif/program_proof/demos")
            .join(path.file_name());
        create_solution(&src_path, &dst_path)?;
    }
    Ok(())
}

pub fn create_student_repo(out: &Path) -> Result<(), anyhow::Error> {
    // Create out directory if necessary
    fs::create_dir_all(out)
        .with_context(|| format!("could not create output directory for student repo"))?;
    let out = &out
        .canonicalize()
        .context("Failed to canonicalize output path")?;
    // Change working directory to the sys-verif-solutions repo (parent of template)
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    std::env::set_current_dir(Path::new(manifest_dir).parent().unwrap())
        .context("Failed to set working directory")?;

    create_assignments(out).with_context(|| format!("could not create assignments"))?;
    create_notes(out).with_context(|| format!("could not create lecture notes"))?;
    create_demos(out).with_context(|| format!("could not create demos"))?;
    copy_static(out).with_context(|| format!("could not copy static files"))?;
    copy_software_foundations(out)
        .with_context(|| format!("could not copy Software Foundations"))?;
    copy_go(out).with_context(|| format!("could not copy Go"))?;

    Ok(())
}
