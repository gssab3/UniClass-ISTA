@echo off
echo Inizio stress test Database Orari (50 richieste)...
:: Sostituisci l'URL se necessario.
:: Parametri ipotizzati: corso=Informatica, anno=1 (basato su struttura standard universitaria)

FOR /L %%i IN (1,1,50) DO (
   curl -s -o nul "http://localhost:8080/UniClass/cercaOrario?corso=Informatica&anno=1"
)

echo Test Orari completato.