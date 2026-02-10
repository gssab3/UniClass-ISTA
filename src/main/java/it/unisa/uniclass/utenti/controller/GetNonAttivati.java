package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory; // USIAMO L'INTERFACCIA
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetNonAttivati", value = "/GetNonAttivati")
public class GetNonAttivati extends HttpServlet {

    @EJB
    private UserDirectory userDirectory;

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            // Recupera tutti gli utenti tramite Facade
            List<Utente> tutti = userDirectory.getTuttiGliUtenti();

            JSONArray jsonArray = new JSONArray();

            for (Utente u : tutti) {
                // Filtra solo gli Accademici non attivati
                if (u instanceof Accademico) {
                    Accademico acc = (Accademico) u;
                    if (!acc.isAttivato()) {
                        JSONObject jsonUtente = new JSONObject();
                        jsonUtente.put("email", acc.getEmail());
                        jsonUtente.put("matricola", acc.getMatricola());
                        // Usa toString() del Ruolo per il campo "tipo"
                        jsonUtente.put("tipo", acc.getRuolo() != null ? acc.getRuolo().toString() : "");
                        jsonArray.put(jsonUtente);
                    }
                }
            }
            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");
            resp.getWriter().write(jsonArray.toString());

        } catch (Exception e) {
            req.getServletContext().log("Error processing GetNonAttivati", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (Exception ignored) {}
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        doGet(req, resp);
    }
}