#![allow(clippy::needless_return)]
use app::App;
use clap::Parser as _;

mod app;
mod assignment;
pub mod coq;
mod debug_print;
mod demo_print;
pub mod literate;
mod student_repo;
pub mod template;
mod website;

fn main() -> Result<(), anyhow::Error> {
    let app = App::parse();
    app.exec()
}
