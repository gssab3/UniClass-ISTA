package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.RestoService;
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

@WebServlet(name = "getResto", value = "/getResto")
public class getResto extends HttpServlet {

    // Non serve più CorsoLaureaService se usiamo il metodo per nome stringa
    @EJB
    private RestoService restoService;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        response.setContentType("application/json");
        response.setCharacterEncoding("UTF-8");

        try (PrintWriter printWriter = response.getWriter()) {
            String nomeCorso = request.getParameter("corsoLaurea");
            JSONArray jsonArray = new JSONArray();

            if (nomeCorso != null && !nomeCorso.trim().isEmpty()) {
                // USIAMO IL METODO CHE ACCETTA LA STRINGA (presente nel tuo Service)
                List<Resto> resti = restoService.trovaRestiCorsoLaurea(nomeCorso);

                if (resti != null) {
                    for (Resto resto : resti) {
                        JSONObject restoJson = new JSONObject();
                        restoJson.put("id", resto.getId());
                        restoJson.put("nome", resto.getNome());
                        jsonArray.put(restoJson);
                    }
                }
            }

            // Scrive il JSON (sarà [] se vuoto, che è corretto per il JS)
            printWriter.println(jsonArray.toString());

        } catch (Exception e) {
            // Log dell'errore nella console del server (Eclipse/IntelliJ)
            e.printStackTrace();
            response.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        doGet(request, response);
    }
}