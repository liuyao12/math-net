# math-net network explorer

This is the first interactive view of the typed proposition graph. It reads
the Fermat example from `../MathNetwork/Graph/fermat.json` and exposes:

- node-kind and relationship filters;
- proof-family focus;
- search across labels, statements, methods, descriptions, and tags;
- drag, zoom, and click-to-inspect graph navigation;
- typed relationship rows linking the selected node to nearby ramifications.

Serve the repository root so the browser can load the graph JSON:

```sh
python3 -m http.server 4173
```

Then open <http://localhost:4173/web/>.
