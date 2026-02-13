package it.unisa.uniclass.testing.unit.orari.controller;

import it.unisa.uniclass.orari.controller.cercaOrario;
import it.unisa.uniclass.orari.model.*;
import it.unisa.uniclass.orari.service.*;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.reflect.Field;
import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

@DisplayName("Test per il controller cercaOrario")
class cercaOrarioTest {

    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    private CorsoLaureaService corsoService;
    private RestoService restoService;
    private AnnoDidatticoService annoService;
    private LezioneService lezioneService;

    private cercaOrario servlet;

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

        servlet = new cercaOrario();

        corsoService = mock(CorsoLaureaService.class);
        restoService = mock(RestoService.class);
        annoService = mock(AnnoDidatticoService.class);
        lezioneService = mock(LezioneService.class);

        inject(servlet, "corsoLaureaService", corsoService);
        inject(servlet, "restoService", restoService);
        inject(servlet, "annoDidatticoService", annoService);
        inject(servlet, "lezioneService", lezioneService);

        when(request.getRequestDispatcher("/OrarioSingolo.jsp")).thenReturn(dispatcher);
    }

    // ---------------------------------------------------------
    // DOPOST - FLUSSO COMPLETO
    // ---------------------------------------------------------

    @Test
    @DisplayName("doPost flusso completo corretto")
    void testDoPostFlussoCompleto() throws Exception {

        // Parametri della richiesta
        when(request.getParameter("corsoLaurea")).thenReturn("Informatica");
        when(request.getParameter("resto")).thenReturn("Resto 0");
        when(request.getParameter("anno")).thenReturn("2023-2024");

        // Mock dei servizi
        CorsoLaurea corso = mock(CorsoLaurea.class);
        when(corso.getId()).thenReturn(1L);

        Resto resto = mock(Resto.class);
        when(resto.getNome()).thenReturn("Resto 0");
        when(resto.getId()).thenReturn(2L);

        AnnoDidattico anno = mock(AnnoDidattico.class);
        when(anno.getAnno()).thenReturn("2023-2024");
        when(anno.getId()).thenReturn(3);

        // Liste simulate dai servizi
        List<Resto> resti = List.of(resto);
        List<AnnoDidattico> anni = List.of(anno);

        List<Lezione> lezioni = new ArrayList<>();
        lezioni.add(new Lezione(
                1,
                Time.valueOf("09:00:00"),
                Time.valueOf("11:00:00"),
                Giorno.LUNEDI,
                null, null, null
        ));

        // Stub dei servizi
        when(corsoService.trovaCorsoLaurea("Informatica")).thenReturn(corso);
        when(restoService.trovaRestiCorsoLaurea("Informatica")).thenReturn(resti);
        when(annoService.trovaTuttiCorsoLaurea(1L)).thenReturn(anni);
        when(lezioneService.trovaLezioniCorsoLaureaRestoAnno(1L, 2L, 3))
                .thenReturn(lezioni);

        // Esecuzione della servlet
        servlet.doPost(request, response);

        // Verifica degli attributi impostati
        verify(request).setAttribute("lezioni", lezioni);
        verify(request).setAttribute("corsoLaurea", corso);
        verify(request).setAttribute("resto", resto);
        verify(request).setAttribute("anno", anno);
        verify(dispatcher).forward(request, response);
    }


    // ---------------------------------------------------------
    // DOPOST - CORSO NON TROVATO
    // ---------------------------------------------------------

    @Test
    @DisplayName("doPost corso non trovato")
    void testDoPostCorsoNonTrovato() throws Exception {

        when(request.getParameter("corsoLaurea")).thenReturn("XXX");
        when(corsoService.trovaCorsoLaurea("XXX")).thenReturn(null);

        servlet.doPost(request, response);

        verify(request).setAttribute(eq("error"), anyString());
        verify(dispatcher).forward(request, response);
    }

    // ---------------------------------------------------------
    // DOGET
    // ---------------------------------------------------------

    @Test
    @DisplayName("doGet delega a doPost")
    void testDoGetDelegation() throws Exception {

        when(request.getParameter("corsoLaurea")).thenReturn("XXX");
        when(corsoService.trovaCorsoLaurea("XXX")).thenReturn(null);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }
}
