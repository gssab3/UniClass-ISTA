package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.LezioneService;
import it.unisa.uniclass.orari.service.RestoService;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.Comparator;
import java.util.List;

@WebServlet(name = "cercaOrarioServlet", value = "/cercaOrario")
public class cercaOrario extends HttpServlet {

    // Injection dei servizi
    @EJB private CorsoLaureaService corsoLaureaService;
    @EJB private RestoService restoService;
    @EJB private AnnoDidatticoService annoDidatticoService;
    @EJB private LezioneService lezioneService;

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            String corsoNome = request.getParameter("corsoLaurea");
            String restoNome = request.getParameter("resto");
            String annoNome = request.getParameter("anno");

            // 1. Recupero Corso di Laurea
            CorsoLaurea corsoLaurea = corsoLaureaService.trovaCorsoLaurea(corsoNome);
            if (corsoLaurea == null) {
                throw new IllegalArgumentException("Corso di laurea non trovato: " + corsoNome);
            }

            // 2. Recupero Resto
            Resto resto = restoService.trovaRestoNomeCorso(restoNome, corsoLaurea);

            // 3. Recupero Anno
            AnnoDidattico annoDidattico = annoDidatticoService.trovaTuttiCorsoLaureaNome(corsoLaurea.getId(), annoNome);

            if (resto != null && annoDidattico != null) {
                // 4. Recupero Lezioni
                List<Lezione> lezioni = lezioneService.trovaLezioniCorsoLaureaRestoAnno(
                        corsoLaurea.getId(), resto.getId(), annoDidattico.getId()
                );

                // Ordinamento (Java 8 stream style o classico, mantengo il tuo)
                lezioni.sort(Comparator.comparing(Lezione::getGiorno).thenComparing(Lezione::getOraInizio));

                request.setAttribute("lezioni", lezioni);
                request.setAttribute("corsoLaurea", corsoLaurea);
                request.setAttribute("resto", resto);
                request.setAttribute("anno", annoDidattico);
            } else {
                // Gestione caso dati mancanti (opzionale: messaggio errore specifico)
                request.setAttribute("error", "Dati di ricerca non validi (Resto o Anno non trovati).");
            }

            request.getRequestDispatcher("/OrarioSingolo.jsp").forward(request, response);

        } catch (Exception e) {
            request.getServletContext().log("Error processing orario request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }
}