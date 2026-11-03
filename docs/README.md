# Documentation

Build and serve from the repository root:

```sh
./scripts/build_docs.sh
python3 -m http.server --bind 127.0.0.1 --directory build/docs 8000
```

Open <http://127.0.0.1:8000>.
