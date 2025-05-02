use std::cell::OnceCell;
use tracing::level_filters::LevelFilter;
use tracing_subscriber::EnvFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

const LOCK: OnceCell<()> = OnceCell::new();

pub fn setup() {
    LOCK.get_or_init(|| {
        // Create a tracing layer with the configured tracer
        let tracer = tracing_subscriber::registry();
        let tracer = tracer
            .with(
                EnvFilter::builder()
                    .with_default_directive(LevelFilter::INFO.into())
                    .from_env_lossy(),
            )
            .with(tracing_span_tree::span_tree().aggregate(true))
            .init();
    });
}