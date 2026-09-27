package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.security.Authorization;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetAttivati", value = "/GetAttivati")
public class GetAttivati extends HttpServlet {

    @EJB
    private UserDirectory userDirectory;

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            if (Authorization.require(req, resp, Tipo.PersonaleTA) == null) {
                return;
            }
            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");
            List<Utente> tutti = userDirectory.getTuttiGliUtenti();
            JSONArray jsonArray = new JSONArray();

            for (Utente u : tutti) {
                if (u instanceof Accademico) {
                    Accademico acc = (Accademico) u;
                    if (acc.isAttivato()) {
                        JSONObject jsonUtente = new JSONObject();
                        jsonUtente.put("email", acc.getEmail());
                        jsonArray.put(jsonUtente);
                    }
                }
            }

            resp.getWriter().write(jsonArray.toString());
        } catch (Exception e) {
            req.getServletContext().log("Error processing GetAttivati", e);
            try {
                JSONObject errorResponse = new JSONObject();
                errorResponse.put("error", "Errore durante il recupero degli utenti attivati.");
                resp.setContentType("application/json");
                resp.setCharacterEncoding("UTF-8");
                resp.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
                resp.getWriter().write(errorResponse.toString());
            } catch (Exception ignored) {}
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        doGet(req, resp);
    }
}