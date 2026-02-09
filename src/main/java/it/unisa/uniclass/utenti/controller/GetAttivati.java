package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.io.IOException;
import java.util.List;

@WebServlet(name = "GetAttivati", value = "/GetAttivati")
public class GetAttivati extends HttpServlet {



    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            AccademicoService accademicoService = new AccademicoService();

            List<Accademico> attivati = accademicoService.trovaAttivati(true);

            JSONArray jsonArray = new JSONArray();

            for (Accademico accademico : attivati) {
                JSONObject jsonUtente = new JSONObject();
                jsonUtente.put("email", accademico.getEmail());

                jsonArray.put(jsonUtente);
            }

            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");

            resp.getWriter().write(jsonArray.toString());
        } catch (Exception e) {
            req.getServletContext().log("Error processing GetAttivati request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {

    }
}
