package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.json.JSONObject;

import java.util.List;

@WebServlet(name = "GetNonAttivati", value = "/GetNonAttivati")
public class GetNonAttivati extends HttpServlet {

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            AccademicoService accademicoService = new AccademicoService();

            List<Accademico> nonAttivati = accademicoService.trovaAttivati(false);

            JSONArray jsonArray = new JSONArray();

            for (Accademico accademico : nonAttivati) {
                JSONObject jsonUtente = new JSONObject();
                jsonUtente.put("email", accademico.getEmail());
                jsonUtente.put("matricola", accademico.getMatricola());
                jsonUtente.put("tipo", accademico.getTipo());

                jsonArray.put(jsonUtente);
            }
            resp.setContentType("application/json");
            resp.setCharacterEncoding("UTF-8");

            resp.getWriter().write(jsonArray.toString());
        } catch (Exception e) {
            req.getServletContext().log("Error processing GetNonAttivati request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (Exception ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        doGet(req, resp);
    }
}
