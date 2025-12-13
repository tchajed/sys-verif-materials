//! Cache output from Coq compilation.

use std::{
    fs,
    hash::{DefaultHasher, Hash as _, Hasher as _},
    time::Duration,
};

use anyhow::Context as _;
use rusqlite::Connection;

use crate::coq::coqc::{CoqArgs, CoqConfig, CoqFile};

type Outputs = Vec<String>;

const CACHE_LIFETIME: chrono::Duration = chrono::Duration::hours(24);

/// CoqOutputCache uses an on-disk cache to speed up repeated compilations of a
/// [`CoqFile`] for purposes of getting Coq's output.
///
/// The implementation only keys on the contents of the input, not dependencies
/// (nor system configuration or Coq arguments), so it's recommended to
/// occasionally delete the cache if making significant changes to dependencies.
///
/// Despite the cache invalidation issues, note that this cache only records the
/// Coq output, which is less likely to change. We generally separately build
/// the full Coq file with proper dependency tracking to make sure that the code
/// is valid.
pub struct CoqOutputCache {
    coq_args: CoqArgs,
    conn: Connection,
}

impl CoqOutputCache {
    fn create_database() -> Result<Connection, anyhow::Error> {
        fs::create_dir_all(".template-cache")
            .with_context(|| "could not create cache directory .template-cache")?;
        let conn = Connection::open(".template-cache/coq-output.sqlite3")
            .with_context(|| "could not open cache db")?;
        conn.busy_timeout(Duration::from_secs(5))?;
        // Each database row is a single output, keyed by (input_hash,
        // output_num). It includes a generation timestamp for expiring old
        // entries, which is useful to avoid the cache growing without bound.
        conn.execute(
            "CREATE TABLE IF NOT EXISTS coq_output_cache (
                    input_hash TEXT,
                    output_num INTEGER,
                    output TEXT,
                    timestamp TEXT
                )",
            [],
        )?;
        conn.execute(
            "CREATE INDEX IF NOT EXISTS coq_output_cache_key
            ON coq_output_cache (input_hash, output_num)",
            [],
        )?;
        let old_time = chrono::Local::now() - CACHE_LIFETIME;
        conn.execute(
            "DELETE FROM coq_output_cache WHERE timestamp < ?",
            [&old_time],
        )?;
        Ok(conn)
    }

    pub fn new(coq_args: CoqArgs) -> Self {
        let conn = Self::create_database().expect("could not create cache");
        Self { coq_args, conn }
    }

    fn key(coq_file: &CoqFile) -> String {
        let mut hasher = DefaultHasher::new();
        coq_file.hash(&mut hasher);
        format!("{:016x}", hasher.finish())
    }

    /// Delete all entries from the cache.
    pub fn clear(&self) -> Result<(), anyhow::Error> {
        self.conn.execute("DELETE FROM coq_output_cache", [])?;
        Ok(())
    }

    fn get_cached_outputs(&self, input_hash: &str) -> Result<Option<Outputs>, anyhow::Error> {
        let mut stmt = self.conn.prepare(
            "SELECT output FROM coq_output_cache WHERE input_hash = ? ORDER BY output_num",
        )?;
        let rows = stmt
            .query_map([input_hash], |row| {
                let output: String = row.get(0)?;
                Ok(output)
            })?
            .collect::<Result<Vec<String>, _>>()?;
        let outputs = if rows.is_empty() { None } else { Some(rows) };
        Ok(outputs)
    }

    fn store_cache(&self, input_hash: &str, outputs: &[String]) -> Result<(), anyhow::Error> {
        let time = chrono::Local::now();
        let tx = self.conn.unchecked_transaction()?;
        for (i, output) in outputs.iter().enumerate() {
            tx.execute(
                "INSERT INTO coq_output_cache
                (input_hash, timestamp, output_num, output)
                VALUES (?, ?, ?, ?)",
                (input_hash, time, i as i64, output),
            )?;
        }
        tx.commit()?;
        Ok(())
    }
}

impl CoqConfig for CoqOutputCache {
    fn get_outputs(&self, coq_file: &CoqFile) -> Result<Vec<String>, anyhow::Error> {
        let k = Self::key(coq_file);
        if let Some(outputs) = self.get_cached_outputs(&k)? {
            return Ok(outputs);
        }
        // need to run Coq
        let outputs = self.coq_args.get_outputs(coq_file)?;
        self.store_cache(&k, &outputs)?;
        Ok(outputs)
    }
}
