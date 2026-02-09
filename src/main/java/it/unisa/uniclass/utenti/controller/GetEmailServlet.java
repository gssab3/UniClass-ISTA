package it.unisa.uniclass.utenti.controller;

import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetEmailServlet", value = "/GetEmailServlet")
public class GetEmailServlet extends HttpServlet {

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        AccademicoService accademicoService = new AccademicoService();

        try {
            List<String> emails = accademicoService.retrieveEmail();

            JSONArray jsonArray = new JSONArray(emails);

            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");

            resp.getWriter().write(jsonArray.toString());
        } catch (Exception e) {
            req.getServletContext().log("Error retrieving emails", e);

            // Gestione degli errori
            try {
                JSONObject errorResponse = new JSONObject();
                errorResponse.put("error", "Errore durante il recupero delle email.");

                resp.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
                resp.setContentType("application/json");
                resp.setCharacterEncoding("UTF-8");
                resp.getWriter().write(errorResponse.toString());
            } catch (Exception innerException) {
                req.getServletContext().log("Failed to send error response", innerException);
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        doGet(req, resp);
    }
}
