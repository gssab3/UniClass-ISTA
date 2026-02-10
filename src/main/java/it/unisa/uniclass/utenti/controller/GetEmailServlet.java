package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetEmailServlet", value = "/GetEmailServlet")
public class GetEmailServlet extends HttpServlet {

    @EJB
    private UtenteService utenteService;

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            // Recuperiamo tutti gli utenti per estrarre le email
            List<Utente> utenti = utenteService.getTuttiGliUtenti();
            JSONArray jsonArray = new JSONArray();

            for(Utente u : utenti) {
                jsonArray.put(u.getEmail());
            }

            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");
            resp.getWriter().write(jsonArray.toString());

        } catch (Exception e) {
            req.getServletContext().log("Error retrieving emails", e);
            try {
                JSONObject errorResponse = new JSONObject();
                errorResponse.put("error", "Errore durante il recupero delle email.");
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