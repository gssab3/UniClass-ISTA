package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

@WebServlet(name = "getAnno", value = "/getAnno")
public class getAnno extends HttpServlet {

    @EJB
    private CorsoLaureaService corsoLaureaService;

    @EJB
    private AnnoDidatticoService annoDidatticoService;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        // Impostiamo subito il tipo di risposta per evitare errori di encoding
        response.setContentType("application/json");
        response.setCharacterEncoding("UTF-8");

        try (PrintWriter printWriter = response.getWriter()) {
            String corsoLaureaNome = request.getParameter("corsoLaurea");
            JSONArray jsonArray = new JSONArray();

            System.out.println("DEBUG getAnno - Richiesto corso: " + corsoLaureaNome);

            if (corsoLaureaNome != null && !corsoLaureaNome.isEmpty()) {
                // 1. Cerchiamo il corso tramite il nome
                // NOTA: Assicurati che nel Service esista un metodo che cerca per NOME (String)
                // Se il tuo metodo si aspetta un ID, questo passaggio fallirà.
                CorsoLaurea corsoL = corsoLaureaService.trovaCorsoLaurea(corsoLaureaNome);

                if (corsoL != null) {
                    System.out.println("DEBUG getAnno - Corso trovato, ID: " + corsoL.getId());

                    // 2. Recuperiamo gli anni associati all'ID del corso
                    List<AnnoDidattico> anni = annoDidatticoService.trovaTuttiCorsoLaurea(corsoL.getId());

                    if (anni != null && !anni.isEmpty()) {
                        System.out.println("DEBUG getAnno - Anni trovati: " + anni.size());
                        for (AnnoDidattico anno : anni) {
                            JSONObject annoJson = new JSONObject();
                            annoJson.put("id", anno.getId());
                            // Usiamo "" + per forzare la conversione in stringa se getAnno restituisce un int
                            annoJson.put("nome", "" + anno.getAnno());
                            jsonArray.put(annoJson);
                        }
                    } else {
                        System.out.println("DEBUG getAnno - Nessun anno trovato per questo corso.");
                    }
                } else {
                    System.out.println("DEBUG getAnno - Errore: CorsoLaurea non trovato nel DB con nome: " + corsoLaureaNome);
                }
            }

            // Scriviamo il JSON (anche se vuoto [])
            printWriter.println(jsonArray.toString());
            printWriter.flush();

        } catch (Exception e) {
            e.printStackTrace(); // Stampa l'errore nella console del server
            response.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        doGet(request, response);
    }
}