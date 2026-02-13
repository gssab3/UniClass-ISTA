package it.unisa.uniclass.testing.unit.orari.controller;

import it.unisa.uniclass.orari.controller.EdificioServlet;
import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.dao.AulaRemote;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.*;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Test per EdificioServlet")
class EdificioServletTest {

    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    private AulaRemote aulaDao;
    private LezioneRemote lezioneDao;

    private EdificioServlet servlet;

    private void inject(Object target, String fieldName, Object value) {
        try {
            Field f = target.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(target, value);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @BeforeEach
    void setUp() {

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        servlet = new EdificioServlet();

        aulaDao = mock(AulaRemote.class);
        lezioneDao = mock(LezioneRemote.class);

        inject(servlet, "aulaDao", aulaDao);
        inject(servlet, "lezioneDao", lezioneDao);

        when(request.getRequestDispatcher("edificio.jsp"))
                .thenReturn(dispatcher);
    }

    // ---------------------------------------------------------
    // FLUSSO COMPLETO
    // ---------------------------------------------------------

    @Test
    void testDoGetFlussoCompleto() throws Exception {

        when(request.getParameter("ed")).thenReturn("Edificio A");

        Aula a1 = new Aula();
        a1.setNome("Aula 101");

        Aula a2 = new Aula();
        a2.setNome("Aula 102");

        List<Aula> aule = List.of(a1, a2);

        when(aulaDao.trovaAuleEdificio("Edificio A"))
                .thenReturn(aule);

        when(lezioneDao.trovaLezioniAule("Aula 101"))
                .thenReturn(List.of(mock(Lezione.class)));

        when(lezioneDao.trovaLezioniAule("Aula 102"))
                .thenReturn(List.of(mock(Lezione.class)));

        servlet.doGet(request, response);

        verify(request).setAttribute("aule", aule);
        verify(request).setAttribute(eq("lezioniPerAula"), any(Map.class));
        verify(request).setAttribute("ed", "Edificio A");
        verify(dispatcher).forward(request, response);
    }

    // ---------------------------------------------------------
    // LISTA AULE NULL
    // ---------------------------------------------------------

    @Test
    void testDoGetAuleNull() throws Exception {

        when(request.getParameter("ed")).thenReturn("Edificio X");
        when(aulaDao.trovaAuleEdificio("Edificio X"))
                .thenReturn(null);

        servlet.doGet(request, response);

        verify(request).setAttribute("aule", null);
        verify(request).setAttribute(eq("lezioniPerAula"), any(Map.class));
        verify(dispatcher).forward(request, response);

        verify(lezioneDao, never()).trovaLezioniAule(any());
    }

    // ---------------------------------------------------------
    // PARAMETRO NULL
    // ---------------------------------------------------------

    @Test
    void testDoGetParametroNull() throws Exception {

        when(request.getParameter("ed")).thenReturn(null);
        when(aulaDao.trovaAuleEdificio(null))
                .thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        verify(request).setAttribute(eq("aule"), any(List.class));
        verify(dispatcher).forward(request, response);
    }

    // ---------------------------------------------------------
    // DOPOST DELEGA
    // ---------------------------------------------------------

    @Test
    void testDoPostDelegaADoGet() throws Exception {

        when(request.getParameter("ed")).thenReturn("Edificio A");
        when(aulaDao.trovaAuleEdificio("Edificio A"))
                .thenReturn(new ArrayList<>());

        servlet.doPost(request, response);

        verify(dispatcher).forward(request, response);
    }
}
