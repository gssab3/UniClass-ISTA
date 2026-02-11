package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.dao.AulaRemote;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

@WebServlet("/EdificioServlet")
public class EdificioServlet extends HttpServlet {

    @EJB
    private AulaRemote aulaDao;

    @EJB
    private LezioneRemote lezioneDao;

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        String edificio = request.getParameter("ed");
        List<Aula> aule = aulaDao.trovaAuleEdificio(edificio);

        // Carico le lezioni per ogni aula (manual load)
        Map<String, List<Lezione>> lezioniPerAula = new HashMap<>();
        if (aule != null) {
            for (Aula a : aule) {
                List<Lezione> lezioni = lezioneDao.trovaLezioniAule(a.getNome());
                lezioniPerAula.put(a.getNome(), lezioni);
            }
        }

        request.setAttribute("aule", aule);
        request.setAttribute("lezioniPerAula", lezioniPerAula);
        request.setAttribute("ed", edificio);

        request.getRequestDispatcher("edificio.jsp").forward(request, response);
    }
}
