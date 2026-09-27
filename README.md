[![SonarQube Cloud](https://sonarcloud.io/images/project_badges/sonarcloud-light.svg)](https://sonarcloud.io/summary/new_code?id=gssab3_UniClass-ISTA)
[![Security Rating](https://sonarcloud.io/api/project_badges/measure?project=gssab3_UniClass-ISTA&metric=security_rating)](https://sonarcloud.io/summary/new_code?id=gssab3_UniClass-ISTA)
[![Maintainability Rating](https://sonarcloud.io/api/project_badges/measure?project=gssab3_UniClass-ISTA&metric=sqale_rating)](https://sonarcloud.io/summary/new_code?id=gssab3_UniClass-ISTA)
[![snyk](https://img.shields.io/github/actions/workflow/status/gssab3/UniClass-ISTA/security-scan.yml?label=snyk)](https://github.com/gssab3/UniClass-ISTA/actions/workflows/security-scan.yml)


# UniClass  

UniClass è una piattaforma modulare per la gestione dell'ambiente accademico universitario, progettata per fornire servizi come la visione degli orari delle lezioni, la gestione delle aule, e la gestione degli utenti. Il sistema è progettato per essere facilmente estendibile e personalizzabile, offrendo una gestione centralizzata e una facile integrazione con altri strumenti accademici.

## Funzionalità principali

- **Visione degli orari delle lezioni**: Gli studenti, i docenti e il personale amministrativo possono visualizzare gli orari delle lezioni aggiornati in tempo reale.
- **Gestione delle aule**: Permette di visualizzare la disponibilità delle aule, facilitando la pianificazione delle lezioni e degli eventi.
- **Gestione degli utenti**: Permette l'aggiunta e la gestione degli utenti (studenti, docenti, personale amministrativo) attraverso una piattaforma modulare che consente di personalizzare facilmente i ruoli e i permessi.
- **Sistema modulare**: La piattaforma è progettata con un'architettura modulare che consente di aggiungere nuove funzionalità in modo facile e rapido.

## Architettura

UniClass è costruita con una serie di moduli separati che coprono le diverse funzionalità del sistema. Ogni modulo interagisce con il database per garantire la coerenza e la sincronizzazione dei dati.

### Moduli principali

1. **Gestione Orari**:
    - Permette di visualizzare, aggiungere e aggiornare gli orari delle lezioni.
    - Supporta la visualizzazione per giorno, settimana o mese.

2. **Gestione Aule**:
    - Gestisce la disponibilità delle aule per le lezioni e gli eventi.
    - Permette di verificare la disponibilità in tempo reale.

3. **Gestione Utenti**:
    - Gestisce studenti, docenti e personale amministrativo.
    - Permette la creazione e la gestione di utenti con ruoli specifici.

4. **Interfaccia Web**:
    - Un'interfaccia utente accessibile via browser per la visualizzazione delle informazioni e l'interazione con il sistema.


## Avvio

### Opzione 1: Build locale (Sviluppo)

Per buildare ed eseguire UniClass localmente:

```bash
mvn clean package
docker compose down --volumes --remove-orphans
docker compose build --no-cache
docker compose up
```

### Opzione 2: Usa l'immagine da DockerHub (Produzione)

Per eseguire UniClass usando l'immagine pre-buildata da DockerHub (`gssab3/uniclass-dependability`):

```bash
# Scarica il file docker-compose.prod.yml dalla repository (se non lo hai già)
# oppure usa quello presente nella directory del progetto

# Avvia l'applicazione completa (TomEE + PostgreSQL)
docker compose -f docker-compose.prod.yml up
```

L'applicazione sarà disponibile su `http://localhost:8080/UniClass-Dependability/`

**Nota importante**: Non usare solo `docker run gssab3/uniclass-dependability:latest` perché manca il database PostgreSQL necessario. Usa sempre `docker-compose.prod.yml` che include sia l'applicazione che il database.
