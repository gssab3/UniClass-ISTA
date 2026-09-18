# Report di Dependability (md-thesis)

Questa cartella contiene tutti i file sorgente Markdown per la generazione del report tecnico del progetto UniClass.

L'intero processo di compilazione è **totalmente automatico** e gestito tramite GitHub Actions. Non è richiesta **alcuna installazione locale** (né Pandoc, né LaTeX).

## Il Processo Automatico

Per mantenere il processo semplice, abbiamo implementato un workflow di CI/CD:

1.  Ogni volta che viene fatto un `git push` sui file sorgente in questa cartella (`*.md`, `*.yaml`), una GitHub Action si avvia automaticamente.
2.  L'azione installa Pandoc e LaTeX su un server remoto.
3.  Compila l'intero documento unendo i capitoli, applicando lo stile definito in `metadata.yaml` e generando il PDF.
4.  Infine, l'azione **committa automaticamente il nuovo PDF** (`UniClass_Report.pdf`) nella cartella `output/` di questo stesso progetto.

**Il risultato:** Il PDF nella repository è sempre sincronizzato con i file sorgente Markdown, senza alcuno sforzo manuale.

---

## ✍️ Come Operare

Per modificare il report, segui queste procedure.

### Modificare un Capitolo Esistente

1.  Apri la cartella `chapters/`.
2.  Trova il file `.md` che vuoi modificare (es. `introduzione.md`).
3.  Apporta le tue modifiche e salva il file.
4.  Fai un `commit` e un `push`. L'azione aggiornerà il PDF per te.

### Aggiungere Immagini

1.  Aggiungi la tua immagine (es. `schema.png`) alla cartella `Images/`.
2.  Nel tuo file `.md`, inseriscila usando la sintassi Markdown relativa:
3.  Fai un `commit` e un `push`.

---

## 📄 Come Trovare il Report

Il PDF finale **si trova direttamente in questo progetto**. Non c'è bisogno di scaricarlo da nessun'altra parte.

> Il file è sempre disponibile qui:
> **`Report/md-thesis/output/UniClass_Report.pdf`**

Ricorda solo di eseguire un `git pull` prima di aprirlo, per assicurarti di avere l'ultima versione che è stata compilata automaticamente.

```bash

git pull
