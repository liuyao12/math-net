# math-net network explorer

This is the first interactive view of the typed proposition graph. With no
query parameter it reads the generated project-wide Lean declaration graph.
It exposes:

- node-kind filters and proof-family focus;
- proof-family focus;
- search across labels, statements, methods, descriptions, and tags;
- drag, zoom, and click-to-inspect graph navigation;
- proof-dependency rows showing what is used in the selected proof.

The graph has one edge relation only: `used-in-proof`. An arrow points from a
declaration or source used by a proof to the proof-family node. Verification
badges are node metadata and do not create graph edges.

Serve the repository root so the browser can load the graph JSON:

```sh
python3 -m http.server 4173
```

Then open <http://localhost:4173/web/> for the project-wide network.

To open the curated Fermat starting graph, use
<http://localhost:4173/web/?graph=fermat>.

To open the curated Euler application graph, use
<http://localhost:4173/web/?graph=euler>.
