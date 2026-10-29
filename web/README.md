# Web front end

A static site that runs the decompiler in the browser via WebAssembly. Files are
processed locally in a Web Worker and never uploaded.

## Build

Prerequisites (once):

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-pack      # or: npm install -g wasm-pack
```

Build the wasm package into `www/pkg/`:

```sh
wasm-pack build web --target web --release --out-dir www/pkg
```

(run from the repository root)

## Run locally

Module workers don't load from `file://`, so serve `www/` over HTTP:

```sh
python -m http.server -d web/www 8080
```

then open http://localhost:8080.

## Deploy

The site is hosted on Cloudflare (Workers static assets — the successor to
Cloudflare Pages) at https://lua-decompiler.com. From `web/`:

```sh
npm run build    # wasm-pack build + assemble a clean dist/
npm run deploy   # build, then upload dist/ with wrangler (config: wrangler.jsonc)
```

The first deploy creates the `lua-decompiler` Worker; run `npx wrangler@4 login`
beforehand if you aren't logged in. `dist/` is a plain static folder, so it can
also go to any other static host that serves `.wasm` as `application/wasm`.

If the domain changes, update the canonical/`og:` URLs in `www/index.html`,
`www/robots.txt` and `www/sitemap.xml`.

## Analytics

The site uses Cloudflare Web Analytics (cookieless, page views only — nothing
about the user's file is ever sent). Either:

- host on Cloudflare Pages and turn on Web Analytics for the project (no code
  change needed), or
- on any other host, create a site under Cloudflare dashboard → Analytics & Logs
  → Web Analytics, and paste its token into
  `<meta name="cf-beacon-token" content="">` in `www/index.html`.

With the token empty, no analytics script is loaded.

## Notes

- A Rust panic aborts the wasm instance, so the page discards the worker and
  starts a fresh one after any crash. Jobs that run longer than 60 s are killed
  the same way.
- `.cargo/config.toml` gives the wasm build a 64 MiB shadow stack to match the
  CLI, but the browser's own call-stack limit still applies; extremely deep
  inputs can fail with a stack-overflow error that the CLI would handle.
