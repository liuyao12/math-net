# math-net network explorer

This is the first interactive view of the theorem-centred dependency graph.
With no query parameter it reads the generated project-wide Lean declaration
graph; theorem-specific query parameters change focus, not the underlying
mathematical space.
It exposes:

- node-kind filters and proof-family focus;
- theorem selection from the List of 100;
- three-level neighborhood focus with unrelated nodes faded;
- search across labels, statements, methods, descriptions, and tags;
- drag, zoom, and click-to-inspect graph navigation;
- proof-dependency rows showing what is used in the selected proof.

The graph has one edge relation only: `used-in-proof`. An arrow points from a
declaration or source used by a proof to the proof-family node. Verification
badges are node metadata and do not create graph edges.

Serve the repository root so the browser can load the graph JSON and theorem
catalogue:

```sh
python3 -m http.server 4173
```

Then open <http://localhost:4173/web/> for the project-wide network. The
Fermat and Euler data remain available as curated source artifacts, but the
interactive view keeps all theorem nodes in one shared canvas.
