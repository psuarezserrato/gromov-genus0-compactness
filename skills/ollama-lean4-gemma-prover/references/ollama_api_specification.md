# Ollama REST API Specification for Lean 4 Prover

Specification for interfacing with Ollama daemon on `http://localhost:11434`.

---

## 1. Endpoints

### 1. `GET /api/tags`
Retrieves inventory of installed local models.
- **Request Headers:** `{"Content-Type": "application/json"}`
- **Response Format:**
  ```json
  {
    "models": [
      {
        "name": "gemma2:9b",
        "modified_at": "2026-11-01T12:00:00Z",
        "size": 5400000000,
        "digest": "sha256:..."
      }
    ]
  }
  ```

### 2. `POST /api/generate`
Submits raw prompt text with generation options.
- **Payload Schema:**
  ```json
  {
    "model": "gemma2:9b",
    "prompt": "<start_of_turn>user\n...<end_of_turn>\n<start_of_turn>model\n",
    "stream": false,
    "options": {
      "temperature": 0.2,
      "top_p": 0.95,
      "top_k": 50,
      "num_predict": 256,
      "stop": ["<end_of_turn>", "<eos>"]
    }
  }
  ```
- **Response Schema:**
  ```json
  {
    "model": "gemma2:9b",
    "response": "exact Mathlib.Analysis.Hofer.hofer ...",
    "done": true,
    "total_duration": 1250000000,
    "eval_count": 42
  }
  ```

### 3. `POST /api/chat`
Submits message array with role tagging (`system`, `user`, `assistant`).
- **Payload Schema:**
  ```json
  {
    "model": "gemma2:9b",
    "messages": [
      {"role": "system", "content": "You are a Lean 4 formal prover."},
      {"role": "user", "content": "⊢ dist x z ≤ dist x y + dist y z"}
    ],
    "stream": false
  }
  ```

---

## 2. Model Fallback Cascade Specification

When the requested model is not available or unspecified, the client selects the highest available tier from the following ordered cascade:
1. `gemma2:9b` (Primary recommended default)
2. `gemma2:27b` (High-reasoning tier)
3. `codegemma:7b` (Code-specialized checkpoint)
4. `gemma:7b` (Legacy 7B)
5. `gemma2:2b` (Ultra-lightweight fallback)
6. `codegemma:2b`
7. `gemma:2b`
8. First model reported by `/api/tags`
