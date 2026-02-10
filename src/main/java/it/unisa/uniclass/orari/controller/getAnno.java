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
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            String corsoLaurea = request.getParameter("corsoLaurea");
            CorsoLaurea corsoL = corsoLaureaService.trovaCorsoLaurea(corsoLaurea);

            JSONArray jsonArray = new JSONArray();

            if (corsoL != null) {
                List<AnnoDidattico> anni = annoDidatticoService.trovaTuttiCorsoLaurea(corsoL.getId());

                for (AnnoDidattico anno : anni) {
                    JSONObject annoJson = new JSONObject();
                    annoJson.put("id", anno.getId());
                    annoJson.put("nome", anno.getAnno());
                    jsonArray.put(annoJson);
                }
            }

            response.setContentType("application/json");
            response.setCharacterEncoding("UTF-8");

            PrintWriter printWriter = response.getWriter();
            printWriter.println(jsonArray.toString());
            printWriter.flush();
        } catch (Exception e) {
            request.getServletContext().log("Error processing getAnno request", e);
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                request.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }
    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) {
        doGet(request, response);
    }
}