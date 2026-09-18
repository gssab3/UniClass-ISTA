@echo off
echo Inizio stress test Login (50 richieste)...
:: Sostituisci l'URL se necessario. Assumo che il container risponda su localhost:8080/UniClass
:: Se l'app ha un nome diverso nel path, modificalo qui sotto.

FOR /L %%i IN (1,1,50) DO (
   curl -s -o nul -X POST -d "email=test@test.it&password=passwordTest123" http://localhost:8080/UniClass/LoginServlet
)

echo Test Login completato.