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
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

@WebServlet(name = "cercaOrarioServlet", value = "/cercaOrario")
public class cercaOrario extends HttpServlet {

    @EJB private CorsoLaureaService corsoLaureaService;
    @EJB private RestoService restoService;
    @EJB private AnnoDidatticoService annoDidatticoService;
    @EJB private LezioneService lezioneService;

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            String corsoNome = request.getParameter("corsoLaurea");
            String restoNome = request.getParameter("resto");
            String annoNome = request.getParameter("anno");

            System.out.println("Ricerca Orario: Corso=" + corsoNome + ", Resto=" + restoNome + ", Anno=" + annoNome);

            // 1. Recupero Corso di Laurea
            CorsoLaurea corsoLaurea = corsoLaureaService.trovaCorsoLaurea(corsoNome);
            if (corsoLaurea == null) {
                request.setAttribute("error", "Corso di laurea non trovato.");
                request.getRequestDispatcher("/OrarioSingolo.jsp").forward(request, response);
                return;
            }

            // 2. Recupero Resto (Filtraggio manuale per sicurezza)
            List<Resto> restiDisponibili = restoService.trovaRestiCorsoLaurea(corsoNome);
            Resto resto = null;
            if(restiDisponibili != null) {
                for(Resto r : restiDisponibili) {
                    if(r.getNome().equalsIgnoreCase(restoNome)) {
                        resto = r;
                        break;
                    }
                }
            }

            // 3. Recupero Anno (Filtraggio manuale per sicurezza)
            List<AnnoDidattico> anniDisponibili = annoDidatticoService.trovaTuttiCorsoLaurea(corsoLaurea.getId());
            AnnoDidattico annoDidattico = null;
            if(anniDisponibili != null) {
                for(AnnoDidattico a : anniDisponibili) {
                    if(a.getAnno().equalsIgnoreCase(annoNome)) {
                        annoDidattico = a;
                        break;
                    }
                }
            }

            List<Lezione> lezioni = new ArrayList<>();
            if (resto != null && annoDidattico != null) {
                // 4. Recupero Lezioni
                // Assicurati che questo metodo esista nel Service. Se si chiama diversamente, aggiorna qui.
                lezioni = lezioneService.trovaLezioniCorsoLaureaRestoAnno(
                        corsoLaurea.getId(), resto.getId(), annoDidattico.getId()
                );

                // Ordinamento: Giorno ASC, poi Ora Inizio ASC
                if (lezioni != null) {
                    lezioni.sort(Comparator.comparing(Lezione::getGiorno)
                            .thenComparing(Lezione::getOraInizio));
                    System.out.println("Trovate " + lezioni.size() + " lezioni.");
                }
            } else {
                System.out.println("Errore: Resto o Anno non trovati nel DB corrispondente.");
            }

            // Set attributi per la JSP
            request.setAttribute("lezioni", lezioni);
            request.setAttribute("corsoLaurea", corsoLaurea);
            request.setAttribute("resto", resto);
            request.setAttribute("anno", annoDidattico);

            request.getRequestDispatcher("/OrarioSingolo.jsp").forward(request, response);

        } catch (Exception e) {
            e.printStackTrace();
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "Errore interno: " + e.getMessage());
            } catch (IOException ignored) {}
        }
    }

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }
}